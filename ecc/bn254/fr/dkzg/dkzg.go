package dkzg

import (
	"errors"
	"math/big"

	"github.com/consensys/gnark-crypto/ecc"
	"github.com/consensys/gnark-crypto/ecc/bn254"
	"github.com/consensys/gnark-crypto/ecc/bn254/fr"
	"github.com/consensys/gnark-crypto/ecc/bn254/fr/fft"
	"github.com/consensys/gnark-crypto/ecc/bn254/fr/kzg"
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
	G1     []bn254.G1Affine  // G1[i][j] = g^(L_i(\tau[0]) * \tau[1]^j)
	G2     [3]bn254.G2Affine // G2[0] = g2, G2[1] = g2^tau[0], G2[2] = g2^tau[1]
	kzgSRS *kzg.SRS
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

func lagrangeCalc(t int, x fr.Element) fr.Element {
	fieldSize := fr.Modulus()
	multiplicativeGroupSize := new(big.Int).Sub(fieldSize, big.NewInt(1))
	omegaPow := new(big.Int).Div(multiplicativeGroupSize, big.NewInt(int64(mpi.WorldSize)))
	omegaBigInt, _ := new(big.Int).SetString("19103219067921713944291392827692070036145651957329286315305642004821462161904", 10)
	omega := *new(fr.Element).SetBigInt(omegaBigInt)
	// BUG: side channel attack
	omega.Exp(omega, omegaPow)
	omegaT := *new(fr.Element).Exp(omega, big.NewInt(int64(t)))
	omegaI := fr.One()
	x0 := &x
	// Lagrange Polynomial
	lagrange := fr.One()
	for i := 0; i < int(mpi.WorldSize); i++ {
		if i != int(t) {
			up := new(fr.Element).Sub(x0, &omegaI)
			down := new(fr.Element).Sub(&omegaT, &omegaI)
			upDivDown := new(fr.Element).Div(up, down)
			lagrange.Mul(&lagrange, upDivDown)
		}
		omegaI.Mul(&omegaI, &omega)
	}
	return lagrange
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

	tau0 := new(fr.Element).SetBigInt(tau[0])
	// Lagrange Polynomial
	lagrange := lagrangeCalc(int(t), *tau0)

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

	// KZG SRS

	kzgSRS, err := kzg.NewSRS(mpi.WorldSize, tau[0])
	srs.kzgSRS = kzgSRS
	if err != nil {
		return nil, err
	}
	return &srs, nil
}

/*
The distributed commit algorithm computes the following:
	1. Each node has a polynomial f_i(y).
	2. The commit algorithm commits to: F(x, y) = \sum_{i=0}^{M-1} f_i(y) * L_i(x), where L_i(x) is the Lagrange polynomial of i.
	3. The commitment is g^{F(\tau[0], \tau[1])} = \Pi_{i=0}^{M-1} g^{f_i(\tau[1]) * L_i(\tau[0])} = \Pi_{i=0}^{M-1}\Pi_{j=0}^{N-1}f_{i, j} * U^{L_i(\tau[0])*\tau[1]^j}.
*/
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

// implements io.ReaderFrom and io.WriterTo
type PartialOpenedProof struct {
	// Com
	Com Digest
	// Proof
	Proof bn254.G1Affine
	// Eval Share
	Evals []fr.Element
}

// dividePolyByXminusA computes (f-f(a))/(x-a), in canonical basis, in regular form
// f memory is re-used for the result
func dividePolyByXminusA(f []fr.Element, fa, a fr.Element) []fr.Element {

	// first we compute f-f(a)
	f[0].Sub(&f[0], &fa)

	// now we use syntetic division to divide by x-a
	var t fr.Element
	for i := len(f) - 2; i >= 0; i-- {
		t.Mul(&f[i+1], &a)

		f[i].Add(&f[i], &t)
	}

	// the result is of degree deg(f)-1
	return f[1:]
}

/*
Given y=y_0, the big polynomail F(x, y_0) becomes F(x, y_0) = \sum_{i=0}^{M-1} f_i(y_0) * L_i(x).
It now becomes a uni-variate polynomial, let it be F'(x) = \sum_{i=0}^{M-1} f_i(y_0) * L_i(x).
New commitment is g^{F'(\tau[0])} = \Pi_{i=0}^{M-1} g^{f_i(y_0) * L_i(\tau[0])} = \Pi_{i=0}^{M-1}f_i(y_0)g^{G1[i][0]}.

Proof that old commitment is consistent with new commitment:
F(\tau[0], \tau[1]) - F(x, \tau[1]) / (\tau[0] - x) = h(x)
*/
func partialOpen(p []fr.Element, y fr.Element, srs *SRS, nbTasks ...int) (PartialOpenedProof, error) {
	if len(p) == 0 || len(p) > len(srs.G1) {
		return PartialOpenedProof{}, ErrInvalidPolynomialSize
	}

	// Build the next level commitment
	// Eval at F(\tau[0], y) = \sum_{i=0}^{M-1} f_i(y) * L_i(\tau[0])

	var newSlaveCom bn254.G1Affine
	var newCom bn254.G1Affine

	config := ecc.MultiExpConfig{ScalarsMont: true}
	if len(nbTasks) > 0 {
		config.NbTasks = nbTasks[0]
	}

	//compute f_i(y)
	allfY := make([]fr.Element, mpi.WorldSize)

	fY := eval(p, y)
	var fYBigInt big.Int
	fY.ToBigIntRegular(&fYBigInt)

	newSlaveCom.ScalarMultiplication(&srs.G1[0], &fYBigInt)

	// Send the new commitment to the root node
	if mpi.SelfRank == 0 {
		// Root node
		subCom := make([]bn254.G1Affine, mpi.WorldSize)
		subCom[0] = newSlaveCom
		for i := 1; i < int(mpi.WorldSize); i++ {
			subComBytes, err := mpi.ReceiveBytes(bn254.SizeOfG1AffineUncompressed, uint64(i))
			if err != nil {
				return PartialOpenedProof{}, err
			}
			subCom[i] = BytesToG1Affine(subComBytes)
		}
		newCom = subCom[0]
		for i := 1; i < int(mpi.WorldSize); i++ {
			newCom.Add(&newCom, &subCom[i])
		}
		// Send the final commitment to all compute nodes
		for i := 1; i < int(mpi.WorldSize); i++ {
			if err := mpi.SendBytes(G1AffineToBytes(newCom), uint64(i)); err != nil {
				return PartialOpenedProof{}, err
			}
		}
	} else {
		// Other nodes
		if err := mpi.SendBytes(G1AffineToBytes(newSlaveCom), 0); err != nil {
			return PartialOpenedProof{}, err
		}
		// Receive the final commitment from the root node
		finalResBytes, err := mpi.ReceiveBytes(bn254.SizeOfG1AffineUncompressed, 0)
		if err != nil {
			return PartialOpenedProof{}, err
		}
		newCom = BytesToG1Affine(finalResBytes)
	}

	// Compute the proof
	// F'(X, Y) = (F(X, Y) - F(X, y)) / (Y - y)
	// F'(X, Y) = \sum_{i=0}^{M-1} (f_i(Y) * L_i(X) - f_i(y) * L_i(X)) / (Y - y)
	// F'(X, Y) = \sum_{i=0}^{M-1} (f_i(Y) - f_i(y)) / (Y - y) * L_i(X)
	// F'(\tau[0], \tau[1]) = \sum_{i=0}^{M-1} (f_i(\tau[1]) - f_i(y)) / (\tau[1] - y) * L_i(\tau[0])
	// Let h(Y) = (f_i(Y) - f_i(y)) / (Y - y) = \sum_{j=0}^{N-2} h_j * Y^j
	// F'(\tau[0], \tau[1]) = \sum_{i=0}^{M-1} \sum_{j=0}^{N-2} h_j * \tau[1]^j * L_i(\tau[0])
	// g^{F'(\tau[0], \tau[1])} = \Pi_{i=0}^{M-1} \Pi_{j=0}^{N-2} g^{h_j * \tau[1]^j * L_i(\tau[0])}
	// g^{F'(\tau[0], \tau[1])} = \Pi_{i=0}^{M-1} \Pi_{i=0}^{N-2} (G1[i][j])^{h_i}

	// Compute h_i
	_p := make([]fr.Element, len(p))
	copy(_p, p)
	h := dividePolyByXminusA(_p, fY, y)
	var hCommit bn254.G1Affine
	hCommit.MultiExp(srs.G1[:len(p)], h, config)

	// Aggregate the hCommit
	if mpi.SelfRank == 0 {
		// Root node
		allfY[0] = fY
		subCom := make([]bn254.G1Affine, mpi.WorldSize)
		subCom[0] = hCommit
		for i := 1; i < int(mpi.WorldSize); i++ {
			subComBytes, err := mpi.ReceiveBytes(bn254.SizeOfG1AffineUncompressed, uint64(i))
			if err != nil {
				return PartialOpenedProof{}, err
			}
			subCom[i] = BytesToG1Affine(subComBytes)

			slavefYBytes, err := mpi.ReceiveBytes(32, uint64(i))
			if err != nil {
				return PartialOpenedProof{}, err
			}
			allfY[i].SetBytes(slavefYBytes)
		}
		hCommit = subCom[0]
		for i := 1; i < int(mpi.WorldSize); i++ {
			hCommit.Add(&hCommit, &subCom[i])
		}
		// Send the final commitment to all compute nodes
		for i := 1; i < int(mpi.WorldSize); i++ {
			if err := mpi.SendBytes(G1AffineToBytes(hCommit), uint64(i)); err != nil {
				return PartialOpenedProof{}, err
			}
		}
		// Send the allfY to all compute nodes
		buf := make([]byte, 32*mpi.WorldSize)
		for i := 0; i < int(mpi.WorldSize); i++ {
			ibuf := allfY[i].Bytes()
			copy(buf[i*32:], ibuf[:])
		}
		for i := 1; i < int(mpi.WorldSize); i++ {
			if err := mpi.SendBytes(buf, uint64(i)); err != nil {
				return PartialOpenedProof{}, err
			}
		}
	} else {
		// Other nodes
		if err := mpi.SendBytes(G1AffineToBytes(hCommit), 0); err != nil {
			return PartialOpenedProof{}, err
		}
		fyBytes := fY.Bytes()

		if err := mpi.SendBytes(fyBytes[:], 0); err != nil {
			return PartialOpenedProof{}, err
		}
		// Receive the final commitment from the root node
		finalResBytes, err := mpi.ReceiveBytes(bn254.SizeOfG1AffineUncompressed, 0)
		if err != nil {
			return PartialOpenedProof{}, err
		}
		hCommit = BytesToG1Affine(finalResBytes)

		//Receive the final fY from the root node
		finalfyBytes, err := mpi.ReceiveBytes(32*mpi.WorldSize, 0)
		if err != nil {
			return PartialOpenedProof{}, err
		}
		for i := 0; i < int(mpi.WorldSize); i++ {
			allfY[i].SetBytes(finalfyBytes[i*32 : (i+1)*32])
		}
	}

	partialProof := PartialOpenedProof{
		Com:   newCom,
		Proof: hCommit,
		Evals: allfY,
	}
	return partialProof, nil
}

// implements io.ReaderFrom and io.WriterTo
type Proof struct {
	// Proof
	// Evaluation
	Result fr.Element
	Proof  bn254.G1Affine
}

// OpeningProof KZG proof for opening at a single 2-D point.
func Open(p []fr.Element, x fr.Element, y fr.Element, srs *SRS) (Proof, error) {
	PartialProof, err := partialOpen(p, y, srs)
	if err != nil {
		return Proof{}, err
	}

	lagrange := lagrangeCalc(int(mpi.SelfRank), x)

	fieldSize := fr.Modulus()
	multiplicativeGroupSize := new(big.Int).Sub(fieldSize, big.NewInt(1))
	omegaPow := new(big.Int).Div(multiplicativeGroupSize, big.NewInt(int64(mpi.WorldSize)))
	omegaBigInt, _ := new(big.Int).SetString("19103219067921713944291392827692070036145651957329286315305642004821462161904", 10)
	omega := *new(fr.Element).SetBigInt(omegaBigInt)
	// BUG: side channel attack
	omega.Exp(omega, omegaPow)
	_x := fr.One()

	// Compute all kinds of lagrange polynomial
	lags := make([]fr.Element, mpi.WorldSize)
	for i := 0; i < int(mpi.WorldSize); i++ {
		lags[i] = lagrangeCalc(i, _x)
		_x.Mul(&_x, &omega)
	}

	// Compute the proof
	// f(X) = \sum_{i=0}^{M-1} fY[i] * L_i(X)
	if mpi.SelfRank == 0 {
		// Root node
		// f(x) = \sum_{i=0}^{M-1} fY[i] * L_i(x)
		// Get L_i(x) from all compute nodes
		subLagrange := make([]fr.Element, mpi.WorldSize)
		subLagrange[0] = lagrange
		for i := 1; i < int(mpi.WorldSize); i++ {
			subLagrangeBytes, err := mpi.ReceiveBytes(32, uint64(i))
			if err != nil {
				return Proof{}, err
			}
			subLagrange[i].SetBytes(subLagrangeBytes)
		}

		// Compute f(x)
		var res fr.Element
		res.SetZero()
		for i := 0; i < int(mpi.WorldSize); i++ {
			var tmp fr.Element
			tmp.Mul(&subLagrange[i], &PartialProof.Evals[i])
			res.Add(&res, &tmp)
		}

		// compute h(X) = (f(X) - res) / (X - x)
		// compute h(omega^i) for all i
		var hX []fr.Element
		omegaI := fr.One()
		for i := 0; i < int(mpi.WorldSize); i++ {
			var fX fr.Element
			fX.SetZero()
			var LX []fr.Element
			LX[0] = lags[i]
			for j := 1; j < int(mpi.WorldSize); j++ {
				//receive lag from client j
				subLagrangeBytes, err := mpi.ReceiveBytes(32, uint64(j))
				if err != nil {
					return Proof{}, err
				}
				LX[j].SetBytes(subLagrangeBytes)
			}
			for j := 0; j < int(mpi.WorldSize); j++ {
				var tmp fr.Element
				tmp.Mul(&LX[j], &PartialProof.Evals[j])
				fX.Add(&fX, &tmp)
			}
			//hX[i] = (fX - res) / (omega^i - x)
			up := new(fr.Element).Sub(&fX, &res)
			down := new(fr.Element).Sub(&omegaI, &x)
			down.Inverse(down)
			hX[i].Mul(up, down)
			omegaI.Mul(&omegaI, &omega)
		}
		// Align the order of hX
		omegaI = fr.One()
		for i := 0; i < int(mpi.WorldSize); i++ {
			hX[i].Mul(&hX[i], &omegaI)
			omegaI.Mul(&omegaI, &omega)
		}
		// Now hX is evaluation of h(x) * x, degree is M - 1
		// Inverse fft to get coefficient of h(x) * x
		domain := fft.NewDomain(mpi.WorldSize)
		_hX := make([]fr.Element, mpi.WorldSize)
		copy(_hX, hX)
		domain.FFTInverse(_hX, fft.DIF)
		fft.BitReverse(_hX)
		// Now _hX is coefficient of h(x) * x, degree is M - 1

		// Commit to _hx
		commit, err := kzg.Commit(_hX, srs.kzgSRS)
		if err != nil {
			return Proof{}, err
		}
		finalProof := Proof{
			Result: res,
			Proof:  commit,
		}
		//Send final proof to all compute nodes
		for i := 1; i < int(mpi.WorldSize); i++ {
			ProofBytes := G1AffineToBytes(finalProof.Proof)
			ResultBytes := finalProof.Result.Bytes()
			err = mpi.SendBytes(ProofBytes, uint64(i))
			if err != nil {
				return Proof{}, err
			}
			err = mpi.SendBytes(ResultBytes[:], uint64(i))
			if err != nil {
				return Proof{}, err
			}
		}
		return finalProof, nil
	} else {
		// Send L_i(x) to the root node
		lagBytes := lagrange.Bytes()
		if err := mpi.SendBytes(lagBytes[:], 0); err != nil {
			return Proof{}, err
		}

		for i := 0; i < int(mpi.WorldSize); i++ {
			// Send L_rank(omega^i) to the root node
			lagBytes := lags[i].Bytes()
			if err := mpi.SendBytes(lagBytes[:], 0); err != nil {
				return Proof{}, err
			}
		}

		// Get the final result from the root node
		ProofBytes, err := mpi.ReceiveBytes(bn254.SizeOfG1AffineUncompressed, 0)
		if err != nil {
			return Proof{}, err
		}
		ResultBytes, err := mpi.ReceiveBytes(32, 0)
		if err != nil {
			return Proof{}, err
		}
		proof := BytesToG1Affine(ProofBytes)
		var Result fr.Element
		Result.SetBytes(ResultBytes)
		finalProof := Proof{
			Result: Result,
			Proof:  proof,
		}
		return finalProof, nil
	}
}
