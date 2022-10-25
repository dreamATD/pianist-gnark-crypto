package dkzg

import (
	"errors"
	"math/big"

	"github.com/consensys/gnark-crypto/ecc"
	"github.com/consensys/gnark-crypto/ecc/bn254"
	"github.com/consensys/gnark-crypto/ecc/bn254/fr"
	"github.com/sunblaze-ucb/simpleMPI/mpi"
)

var (
	ErrInvalidNbDigests              = errors.New("number of digests is not the same as the number of polynomials")
	ErrInvalidPolynomialSize         = errors.New("invalid polynomial size (larger than SRS or == 0)")
	ErrVerifyOpeningProof            = errors.New("can't verify opening proof")
	ErrVerifyBatchOpeningSinglePoint = errors.New("can't verify batch opening proof at single point")
	ErrMinSRSSize                    = errors.New("minimum srs size is 2")
)

// Digest commitment of a polynomial.
type Digest = bn254.G1Affine

type SRS struct {
	G1 []bn254.G1Affine  // G1[i][j] = g^(L_i(j)) * h^j, g = g1^tau[0], h = g1^tau[1]
	G2 [3]bn254.G2Affine // G2[0] = g2, G2[1] = g2^tau[0], G2[2] = g2^tau[1]
}

// eval returns p(point) where p is interpreted as a polynomial
// ∑_{i<len(p)}p[i]Xⁱ
func eval(p []fr.Element, point fr.Element) fr.Element {
	var res fr.Element
	n := len(p)
	res.Set(&p[n-1])
	for i := n - 2; i >= 0; i-- {
		res.Mul(&res, &point).Add(&res, &p[i])
	}
	return res
}

// NewSRS returns a new SRS using alpha as randomness source
//
// In production, a SRS generated through MPC should be used.
//
// implements io.ReaderFrom and io.WriterTo
func NewSRS(size uint64, tau []*big.Int) (*SRS, error) {

	_, _, gen1Aff, gen2Aff := bn254.Generators()
	t := mpi.SelfRank

	//prepare lagrange polynomial
	//L_t(\tau[0]) = \prod_{i=0, i!=t}^{n-1}(\tau[0]-omega^i)/(omega^t-omega^i)
	// Multiplicative Generator
	fieldSize := fr.Modulus()
	multiplicativeGroupSize := new(big.Int).Sub(fieldSize, big.NewInt(1))
	omegaPow := new(big.Int).Div(multiplicativeGroupSize, big.NewInt(int64(mpi.WorldSize)))
	omegaBigInt, _ := new(big.Int).SetString("6506949774839052718110406215085119770091102268120408611511048664532142289545", 10)
	omega := *new(fr.Element).SetBigInt(omegaBigInt)

	// BUG: side channel attack
	omega.Exp(omega, omegaPow)
	omegaT := *new(fr.Element).Exp(omega, big.NewInt(int64(t)))
	omegaI := fr.One()
	tau0 := new(fr.Element).SetBigInt(tau[0])
	// Lagrange Polynomial
	lagrange := fr.One()
	for i := 0; i < int(mpi.WorldSize); i++ {
		if i != int(t) {
			up := new(fr.Element).Sub(tau0, &omegaI)
			down := new(fr.Element).Sub(&omegaT, &omegaI)
			upDivDown := new(fr.Element).Div(up, down)
			lagrange.Mul(&lagrange, upDivDown)
		}
		omegaI.Mul(&omegaI, &omega)
	}

	var srs SRS

	var alpha fr.Element
	alpha.SetBigInt(tau[1])

	srs.G2[0] = gen2Aff
	srs.G2[1].ScalarMultiplication(&gen2Aff, tau[0])
	srs.G2[2].ScalarMultiplication(&gen2Aff, tau[1])

	lagBigInt := new(big.Int)
	lagrange.ToBigIntRegular(lagBigInt)
	srs.G1[0].ScalarMultiplication(&gen1Aff, lagBigInt)

	alphas := make([]fr.Element, size-1)
	alphas[0] = alpha
	alphas[0].Mul(&alphas[0], &lagrange)
	for i := 1; i < len(alphas); i++ {
		alphas[i].Mul(&alphas[i-1], &alpha)
	}
	for i := 0; i < len(alphas); i++ {
		alphas[i].FromMont()
	}
	g1s := bn254.BatchScalarMultiplicationG1(&gen1Aff, alphas)
	copy(srs.G1[1:], g1s)

	return &srs, nil
}

type PartialOpenedProof struct {
	// Com
	Com Digest
	// Proof
	Proof bn254.G1Affine
}

func Commit(p []fr.Element, srs *SRS, nbTasks ...int) (Digest, error) {
	// Each compute node computes the commitment of its own polynomial
	// and sends the commitment to the root node
	// The root node computes the final commitment
	// and sends the final commitment to all compute nodes

	if len(p) == 0 || len(p) > len(srs.G1) {
		return Digest{}, ErrInvalidPolynomialSize
	}

	var res bn254.G1Affine

	config := ecc.MultiExpConfig{ScalarsMont: true}
	if len(nbTasks) > 0 {
		config.NbTasks = nbTasks[0]
	}

	if _, err := res.MultiExp(srs.G1[:len(p)], p, config); err != nil {
		return Digest{}, err
	}

	// Aggregate commitments
	if mpi.SelfRank == 0 {
		//Root node
		subCom := make([]Digest, mpi.WorldSize)
		subCom[0] = res
		for i := 1; i < int(mpi.WorldSize); i++ {
			subComBytes, err := mpi.ReceiveBytes(bn254.SizeOfG1AffineUncompressed, uint64(i))
			if err != nil {
				return Digest{}, err
			}
			subCom[i] = BytesToG1Affine(subComBytes)
		}
		finalRes := subCom[0]
		for i := 1; i < int(mpi.WorldSize); i++ {
			finalRes.Add(&finalRes, &subCom[i])
		}
		// Send the final commitment to all compute nodes
		for i := 1; i < int(mpi.WorldSize); i++ {
			if err := mpi.SendBytes(G1AffineToBytes(finalRes), uint64(i)); err != nil {
				return Digest{}, err
			}
		}
		return finalRes, nil
	} else {
		// Other nodes
		if err := mpi.SendBytes(G1AffineToBytes(res), 0); err != nil {
			return Digest{}, err
		}
		// Receive the final commitment from the root node
		finalResBytes, err := mpi.ReceiveBytes(bn254.SizeOfG1AffineUncompressed, 0)
		if err != nil {
			return Digest{}, err
		}
		return BytesToG1Affine(finalResBytes), nil
	}
}

// OpeningProof KZG proof for opening at a single 2-D point.
//
// implements io.ReaderFrom and io.WriterTo
type OpeningProof struct {
	// H quotient polynomial (f - f(z))/(x-z)
	H bn254.G1Affine

	// ClaimedValue purported value
	ClaimedValue fr.Element
}
