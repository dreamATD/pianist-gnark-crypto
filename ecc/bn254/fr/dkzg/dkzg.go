package dkzg

import (
	"errors"
	"fmt"
	"hash"
	"math/big"
	"runtime/debug"
	"sync"

	"github.com/consensys/gnark-crypto/ecc"
	"github.com/consensys/gnark-crypto/ecc/bn254"
	"github.com/consensys/gnark-crypto/ecc/bn254/fr"
	fiatshamir "github.com/consensys/gnark-crypto/fiat-shamir"
	"github.com/consensys/gnark-crypto/internal/parallel"
	"github.com/sunblaze-ucb/simpleMPI/mpi"
)

var (
	ErrInvalidNbDigests              = errors.New("dkzg: number of digests is not the same as the number of polynomials")
	ErrInvalidPolynomialSize         = errors.New("dkzg: invalid polynomial size (larger than SRS or == 0)")
	ErrVerifyOpeningProof            = errors.New("dkzg: can't verify opening proof")
	ErrVerifyBatchOpeningSinglePoint = errors.New("dkzg: can't verify batch opening proof at single point")
	ErrMinSRSSize                    = errors.New("dkzg: minimum srs size is 2")
)

// Digest commitment of a polynomial.
type Digest = bn254.G1Affine

type SRS struct {
	G1 []bn254.G1Affine  // G1[i][j] = g^(L_i(\tau[0]) * \tau[1]^j)
	G2 [2]bn254.G2Affine // G2[0] = g2, G2[1] = g2^tau[0], G2[2] = g2^tau[1]
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

func init() {
	mpi.WorldInit("ip.txt", "/home/farmer/.ssh/id_rsa", "farmer")
}

func lagrangeCalc(t int, tau0 fr.Element) fr.Element {
	m := big.NewInt(int64(mpi.WorldSize))
	mField := new(fr.Element).SetBigInt(m)
	fieldSize := fr.Modulus()
	multiplicativeGroupSize := new(big.Int).Sub(fieldSize, big.NewInt(1))
	omegaPow := new(big.Int).Div(multiplicativeGroupSize, m)
	omegaBigInt, _ := new(big.Int).SetString("19103219067921713944291392827692070036145651957329286315305642004821462161904", 10)
	omega := *new(fr.Element).SetBigInt(omegaBigInt)
	// BUG: side channel attack
	omega.Exp(omega, omegaPow)

	// R_t(tau0) = ((tau[0]^m - 1) * omega^t) / (m * (tau[0] - omega^t))
	var lagTau0, omegaPowT, denominator fr.Element
	omegaPowT.Exp(omega, big.NewInt(int64(t)))
	one := fr.One()
	denominator.Sub(&tau0, &omegaPowT).Mul(&denominator, mField)
	lagTau0.Exp(tau0, m).Sub(&lagTau0, &one).Mul(&lagTau0, &omegaPowT).Div(&lagTau0, &denominator)
	return lagTau0
}

// NewSRS returns a new SRS using alpha as randomness source
//
// In production, a SRS generated through MPC should be used.
//
// implements io.ReaderFrom and io.WriterTo
func NewSRS(size uint64, tau []*big.Int) (*SRS, error) {

	_, _, gen1Aff, gen2Aff := bn254.Generators()
	t := mpi.SelfRank

	tau0 := new(fr.Element).SetBigInt(tau[0])
	// Lagrange Polynomial
	lagTau0 := lagrangeCalc(int(t), *tau0)

	var srs SRS

	var alpha fr.Element
	alpha.SetBigInt(tau[1])

	srs.G2[0] = gen2Aff
	srs.G2[1].ScalarMultiplication(&gen2Aff, tau[1])

	lagBigInt := new(big.Int)
	lagTau0.ToBigIntRegular(lagBigInt)
	srs.G1 = make([]bn254.G1Affine, size)
	srs.G1[0].ScalarMultiplication(&gen1Aff, lagBigInt)

	alphas := make([]fr.Element, size-1)
	alphas[0] = alpha
	alphas[0].Mul(&alphas[0], &lagTau0)
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
		fmt.Println(string(debug.Stack()))
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
		return finalRes, nil
	}

	// Other nodes
	if err := mpi.SendBytes(G1AffineToBytes(res), 0); err != nil {
		return Digest{}, err
	}
	// Only the root node returns the final commitment
	return Digest{}, nil
}

// implements io.ReaderFrom and io.WriterTo
type OpeningProof struct {
	// H quotient polynomial (f(Y, X) - f(Y, alpha)) / (X - alpha)
	H bn254.G1Affine

	// ClaimedDigest purported the digest of value
	ClaimedDigest bn254.G1Affine
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
func Open(p []fr.Element, y fr.Element, srs *SRS, nbTasks ...int) (OpeningProof, []fr.Element, error) {
	if len(p) == 0 || len(p) > len(srs.G1) {
		fmt.Println(string(debug.Stack()))
		return OpeningProof{}, nil, ErrInvalidPolynomialSize
	}

	// Build the next level commitment
	// Eval at F(\tau[0], y) = \sum_{i=0}^{M-1} f_i(y) * L_i(\tau[0])
	config := ecc.MultiExpConfig{ScalarsMont: true}
	if len(nbTasks) > 0 {
		config.NbTasks = nbTasks[0]
	}

	// compute f_i(y)
	fY := eval(p, y)
	var fYBigInt big.Int
	fY.ToBigIntRegular(&fYBigInt)

	// digest of f_i(y)
	var comFY bn254.G1Affine
	comFY.ScalarMultiplication(&srs.G1[0], &fYBigInt)

	// compute H
	_p := make([]fr.Element, len(p))
	copy(_p, p)
	h := dividePolyByXminusA(_p, fY, y)

	_p = nil // h re-use this memory

	// commit to H
	comH, err := Commit(h, srs)
	if err != nil {
		return OpeningProof{}, nil, err
	}

	// Send the new commitment to the root node
	if mpi.SelfRank == 0 {
		// Root node
		allFY := make([]fr.Element, mpi.WorldSize)
		allComFY := make([]bn254.G1Affine, mpi.WorldSize)
		allComH := make([]bn254.G1Affine, mpi.WorldSize)
		allFY[0] = fY
		allComFY[0] = comFY
		allComH[0] = comH
		for i := 1; i < int(mpi.WorldSize); i++ {
			fYBytes, err := mpi.ReceiveBytes(fr.Bytes, uint64(i))
			if err != nil {
				return OpeningProof{}, nil, err
			}
			allFY[i].SetBytes(fYBytes)
			comFyBytes, err := mpi.ReceiveBytes(bn254.SizeOfG1AffineUncompressed, uint64(i))
			if err != nil {
				return OpeningProof{}, nil, err
			}
			allComFY[i] = BytesToG1Affine(comFyBytes)
			comHBytes, err := mpi.ReceiveBytes(bn254.SizeOfG1AffineUncompressed, uint64(i))
			if err != nil {
				return OpeningProof{}, nil, err
			}
			allComH[i] = BytesToG1Affine(comHBytes)
		}

		comFY = allComFY[0]
		for i := 1; i < int(mpi.WorldSize); i++ {
			comFY.Add(&comFY, &allComFY[i])
		}
		comH = allComH[0]
		for i := 1; i < int(mpi.WorldSize); i++ {
			comH.Add(&comH, &allComH[i])
		}

		return OpeningProof{
			H:             comH,
			ClaimedDigest: comFY,
		}, allFY, nil
	}

	// Other nodes
	fYBytes := fY.Bytes()
	if err := mpi.SendBytes(fYBytes[:], 0); err != nil {
		return OpeningProof{}, nil, err
	}
	if err := mpi.SendBytes(G1AffineToBytes(comFY), 0); err != nil {
		return OpeningProof{}, nil, err
	}
	if err := mpi.SendBytes(G1AffineToBytes(comH), 0); err != nil {
		return OpeningProof{}, nil, err
	}
	return OpeningProof{}, nil, nil
}

// BatchOpeningProof opening proof for many polynomials at the same point
//
// implements io.ReaderFrom and io.WriterTo
type BatchOpeningProof struct {
	// H quotient polynomial Sum_i gamma**i*(f - f(z))/(x-z)
	H bn254.G1Affine

	// ClaimedValues purported values
	ClaimedDigests []bn254.G1Affine
}

// Verify verifies a KZG opening proof at a single point
func Verify(commitment *Digest, proof *OpeningProof, point fr.Element, srs *SRS) error {
	// [f(a)]G₁
	var claimedValueG1Aff bn254.G1Jac
	claimedValueG1Aff.FromAffine(&proof.ClaimedDigest)

	// [f(α) - f(a)]G₁
	var fminusfaG1Jac bn254.G1Jac
	fminusfaG1Jac.FromAffine(commitment)
	fminusfaG1Jac.SubAssign(&claimedValueG1Aff)

	// [-H(α)]G₁
	var negH bn254.G1Affine
	negH.Neg(&proof.H)

	// [α-a]G₂
	var alphaMinusaG2Jac, genG2Jac, alphaG2Jac bn254.G2Jac
	var pointBigInt big.Int
	point.ToBigIntRegular(&pointBigInt)
	genG2Jac.FromAffine(&srs.G2[0])
	alphaG2Jac.FromAffine(&srs.G2[1])
	alphaMinusaG2Jac.ScalarMultiplication(&genG2Jac, &pointBigInt).
		Neg(&alphaMinusaG2Jac).
		AddAssign(&alphaG2Jac)

	// [α-a]G₂
	var xminusaG2Aff bn254.G2Affine
	xminusaG2Aff.FromJacobian(&alphaMinusaG2Jac)

	// [f(α) - f(a)]G₁
	var fminusfaG1Aff bn254.G1Affine
	fminusfaG1Aff.FromJacobian(&fminusfaG1Jac)

	// e([f(α) - f(a)]G₁, G₂).e([-H(α)]G₁, [α-a]G₂) ==? 1
	check, err := bn254.PairingCheck(
		[]bn254.G1Affine{fminusfaG1Aff, negH},
		[]bn254.G2Affine{srs.G2[0], xminusaG2Aff},
	)
	if err != nil {
		return err
	}
	if !check {
		return ErrVerifyOpeningProof
	}
	return nil
}

// BatchOpenSinglePoint creates a batch opening proof at point of a list of polynomials.
// It's an interactive protocol, made non interactive using Fiat Shamir.
//
// * point is the point at which the polynomials are opened.
// * digests is the list of committed polynomials to open, need to derive the challenge using Fiat Shamir.
// * polynomials is the list of polynomials to open, they are supposed to be of the same size.
func BatchOpenSinglePoint(polynomials [][]fr.Element, digests []Digest, point fr.Element, hf hash.Hash, srs *SRS) (BatchOpeningProof, [][]fr.Element, error) {
	// check for invalid sizes
	nbDigests := len(digests)
	if nbDigests != len(polynomials) {
		return BatchOpeningProof{}, nil, ErrInvalidNbDigests
	}

	// TODO ensure the polynomials are of the same size
	largestPoly := -1
	for _, p := range polynomials {
		if len(p) == 0 || len(p) > len(srs.G1) {
			fmt.Println(string(debug.Stack()))
			return BatchOpeningProof{}, nil, ErrInvalidPolynomialSize
		}
		if len(p) > largestPoly {
			largestPoly = len(p)
		}
	}

	// compute the purported values
	claimedValues := make([]fr.Element, len(polynomials))
	claimedDigests := make([]bn254.G1Affine, len(polynomials))
	var wg sync.WaitGroup
	wg.Add(len(polynomials))
	for i := 0; i < len(polynomials); i++ {
		go func(_i int) {
			claimedValues[_i] = eval(polynomials[_i], point)
			var claimedValueBigInt big.Int
			claimedValues[_i].ToBigIntRegular(&claimedValueBigInt)
			claimedDigests[_i].ScalarMultiplication(&srs.G1[0], &claimedValueBigInt)
			wg.Done()
		}(i)
	}
	// derive the challenge γ, binded to the point and the commitments
	gamma, err := deriveGamma(point, digests, hf)
	if err != nil {
		return BatchOpeningProof{}, nil, err
	}

	// ∑ᵢγⁱf(a)
	var fY fr.Element
	chSumGammai := make(chan struct{}, 1)
	go func() {
		// wait for polynomial evaluations to be completed (res.ClaimedValues)
		wg.Wait()
		fY = claimedValues[nbDigests-1]
		for i := nbDigests - 2; i >= 0; i-- {
			fY.Mul(&fY, &gamma).
				Add(&fY, &claimedValues[i])
		}
		close(chSumGammai)
	}()

	// compute ∑ᵢγⁱfᵢ
	// note: if we are willing to paralellize that, we could clone the poly and scale them by
	// gamma n in parallel, before reducing into foldedPolynomials
	foldedPolynomials := make([]fr.Element, largestPoly)
	copy(foldedPolynomials, polynomials[0])
	acc := gamma
	var pj fr.Element
	for i := 1; i < len(polynomials); i++ {
		parallel.Execute(len(polynomials[i]), func(start, end int) {
			for j := start; j < end; j++ {
				pj.Mul(&polynomials[i][j], &acc)
				foldedPolynomials[j].Add(&foldedPolynomials[j], &pj)
			}
		})
		acc.Mul(&acc, &gamma)
	}

	<-chSumGammai

	// compute H
	h := dividePolyByXminusA(foldedPolynomials, fY, point)
	foldedPolynomials = nil // same memory as h

	comH, err := Commit(h, srs)
	if err != nil {
		return BatchOpeningProof{}, nil, err
	}

	// Send the new commitment to the root node
	if mpi.SelfRank == 0 {
		// Root node
		allClaimedValues := make([][]fr.Element, nbDigests)
		allClaimedDigests := make([][]bn254.G1Affine, nbDigests)
		allComH := make([]bn254.G1Affine, mpi.WorldSize)
		allComH[0] = comH
		for k := 0; k < nbDigests; k++ {
			allClaimedValues[k] = make([]fr.Element, mpi.WorldSize)
			allClaimedDigests[k] = make([]bn254.G1Affine, mpi.WorldSize)
			allClaimedValues[k][0] = claimedValues[k]
			allClaimedDigests[k][0] = claimedDigests[k]
			for i := 1; i < int(mpi.WorldSize); i++ {
				claimedValueBytes, err := mpi.ReceiveBytes(fr.Bytes, uint64(i))
				fmt.Println("Received claimed value from", i, ":", claimedValueBytes)
				if err != nil {
					return BatchOpeningProof{}, nil, err
				}
				allClaimedValues[k][i].SetBytes(claimedValueBytes)
				claimedDigestBytes, err := mpi.ReceiveBytes(bn254.SizeOfG1AffineUncompressed, uint64(i))
				if err != nil {
					return BatchOpeningProof{}, nil, err
				}
				allClaimedDigests[k][i] = BytesToG1Affine(claimedDigestBytes)
			}
		}

		for i := 1; i < int(mpi.WorldSize); i++ {
			comHBytes, err := mpi.ReceiveBytes(bn254.SizeOfG1AffineUncompressed, uint64(i))
			if err != nil {
				return BatchOpeningProof{}, nil, err
			}
			allComH[i] = BytesToG1Affine(comHBytes)
		}

		for k := range allClaimedValues {
			claimedDigests[k] = allClaimedDigests[k][0]
			for i := 1; i < int(mpi.WorldSize); i++ {
				claimedDigests[k].Add(&claimedDigests[k], &allClaimedDigests[k][i])
			}
		}
		comH = allComH[0]
		for i := 1; i < int(mpi.WorldSize); i++ {
			comH.Add(&comH, &allComH[i])
		}

		return BatchOpeningProof{
			H:              comH,
			ClaimedDigests: claimedDigests,
		}, allClaimedValues, nil
	}

	fmt.Println("Other nodes")

	// Other nodes
	for k := 0; k < nbDigests; k++ {
		claimedValueBytes := claimedValues[k].Bytes()
		fmt.Println("Sending claimed value", claimedValues[k].String(), k)
		if err := mpi.SendBytes(claimedValueBytes[:], 0); err != nil {
			return BatchOpeningProof{}, nil, err
		}
		if err := mpi.SendBytes(G1AffineToBytes(claimedDigests[k]), 0); err != nil {
			return BatchOpeningProof{}, nil, err
		}

	}
	if err := mpi.SendBytes(G1AffineToBytes(comH), 0); err != nil {
		return BatchOpeningProof{}, nil, err
	}
	fmt.Println("Other nodes done")
	return BatchOpeningProof{}, nil, nil
}

// FoldProof fold the digests and the proofs in batchOpeningProof using Fiat Shamir
// to obtain an opening proof at a single point.
//
// * digests list of digests on which batchOpeningProof is based
// * batchOpeningProof opening proof of digests
// * returns the folded version of batchOpeningProof, Digest, the folded version of digests
func FoldProof(digests []Digest, batchOpeningProof *BatchOpeningProof, point fr.Element, hf hash.Hash) (OpeningProof, Digest, error) {
	nbDigests := len(digests)

	// check consistancy between numbers of claims vs number of digests
	if nbDigests != len(batchOpeningProof.ClaimedDigests) {
		fmt.Println("Catch")
		return OpeningProof{}, Digest{}, ErrInvalidNbDigests
	}

	// derive the challenge γ, binded to the point and the commitments
	gamma, err := deriveGamma(point, digests, hf)
	if err != nil {
		fmt.Println("Catch2")
		return OpeningProof{}, Digest{}, ErrInvalidNbDigests
	}

	// fold the claimed values and digests
	// gammai = [1,γ,γ²,..,γⁿ⁻¹]
	gammai := make([]fr.Element, nbDigests)
	gammai[0].SetOne()
	for i := 1; i < nbDigests; i++ {
		gammai[i].Mul(&gammai[i-1], &gamma)
	}

	foldedDigests, foldedEvaluations, err := fold(digests, batchOpeningProof.ClaimedDigests, gammai)
	if err != nil {
		return OpeningProof{}, Digest{}, err
	}

	// create the folded opening proof
	var res OpeningProof
	res.ClaimedDigest.Set(&foldedEvaluations)
	res.H.Set(&batchOpeningProof.H)

	return res, foldedDigests, nil
}

// BatchVerifySinglePoint verifies a batched opening proof at a single point of a list of polynomials.
//
// * digests list of digests on which opening proof is done
// * batchOpeningProof proof of correct opening on the digests
func BatchVerifySinglePoint(digests []Digest, batchOpeningProof *BatchOpeningProof, point fr.Element, hf hash.Hash, srs *SRS) error {
	return fmt.Errorf("not implemented")
}

// BatchVerifyMultiPoints batch verifies a list of opening proofs at different points.
// The purpose of the batching is to have only one pairing for verifying several proofs.
//
// * digests list of committed polynomials
// * proofs list of opening proofs, one for each digest
// * points the list of points at which the opening are done
func BatchVerifyMultiPoints(digests []Digest, proofs []OpeningProof, points []fr.Element, srs *SRS) error {
	// check consistancy nb proogs vs nb digests
	if len(digests) != len(proofs) || len(digests) != len(points) {
		return ErrInvalidNbDigests
	}

	// if only one digest, call Verify
	if len(digests) == 1 {
		return Verify(&digests[0], &proofs[0], points[0], srs)
	}

	// sample random numbers λᵢ for sampling
	randomNumbers := make([]fr.Element, len(digests))
	randomNumbers[0].SetOne()
	for i := 1; i < len(randomNumbers); i++ {
		_, err := randomNumbers[i].SetRandom()
		if err != nil {
			return err
		}
	}

	// fold the committed quotients compute ∑ᵢλᵢ[Hᵢ(α)]G₁
	var foldedQuotients bn254.G1Affine
	quotients := make([]bn254.G1Affine, len(proofs))
	for i := 0; i < len(randomNumbers); i++ {
		quotients[i].Set(&proofs[i].H)
	}
	config := ecc.MultiExpConfig{ScalarsMont: true}
	_, err := foldedQuotients.MultiExp(quotients, randomNumbers, config)
	if err != nil {
		return nil
	}

	// fold digests and evalCommits
	evalCommits := make([]bn254.G1Affine, len(digests))
	for i := 0; i < len(randomNumbers); i++ {
		evalCommits[i].Set(&proofs[i].ClaimedDigest)
	}

	// fold the digests: ∑ᵢλᵢ[f_i(α)]G₁
	// fold the evals  : ∑ᵢλᵢfᵢ(aᵢ)
	foldedDigests, foldedEvalsCommit, err := fold(digests, evalCommits, randomNumbers)
	if err != nil {
		return err
	}

	// compute foldedDigests = ∑ᵢλᵢ[fᵢ(α)]G₁ - [∑ᵢλᵢfᵢ(aᵢ)]G₁
	foldedDigests.Sub(&foldedDigests, &foldedEvalsCommit)

	// combien the points and the quotients using γᵢ
	// ∑ᵢλᵢ[p_i]([Hᵢ(α)]G₁)
	var foldedPointsQuotients bn254.G1Affine
	for i := 0; i < len(randomNumbers); i++ {
		randomNumbers[i].Mul(&randomNumbers[i], &points[i])
	}
	_, err = foldedPointsQuotients.MultiExp(quotients, randomNumbers, config)
	if err != nil {
		return err
	}

	// ∑ᵢλᵢ[f_i(α)]G₁ - [∑ᵢλᵢfᵢ(aᵢ)]G₁ + ∑ᵢλᵢ[p_i]([Hᵢ(α)]G₁)
	// = [∑ᵢλᵢf_i(α) - ∑ᵢλᵢfᵢ(aᵢ) + ∑ᵢλᵢpᵢHᵢ(α)]G₁
	foldedDigests.Add(&foldedDigests, &foldedPointsQuotients)

	// -∑ᵢλᵢ[Qᵢ(α)]G₁
	foldedQuotients.Neg(&foldedQuotients)

	// pairing check
	// e([∑ᵢλᵢ(fᵢ(α) - fᵢ(pᵢ) + pᵢHᵢ(α))]G₁, G₂).e([-∑ᵢλᵢ[Hᵢ(α)]G₁), [α]G₂)
	check, err := bn254.PairingCheck(
		[]bn254.G1Affine{foldedDigests, foldedQuotients},
		[]bn254.G2Affine{srs.G2[0], srs.G2[1]},
	)
	if err != nil {
		return err
	}
	if !check {
		return ErrVerifyOpeningProof
	}
	return nil

}

// fold folds digests and evaluations using the list of factors as random numbers.
//
// * digests list of digests to fold
// * evaluations list of evaluations to fold
// * factors list of multiplicative factors used for the folding (in Montgomery form)
//
// * Returns ∑ᵢcᵢdᵢ, ∑ᵢcᵢf(aᵢ)
func fold(di []Digest, fai []bn254.G1Affine, ci []fr.Element) (Digest, Digest, error) {
	// length inconsistancy between digests and evaluations should have been done before calling this function
	nbDigests := len(di)

	// fold the claimed values ∑ᵢcᵢf(aᵢ)
	var foldedEvaluations, tmp bn254.G1Affine
	for i := 0; i < nbDigests; i++ {
		var ciBigInt big.Int
		ci[i].ToBigIntRegular(&ciBigInt)
		tmp.ScalarMultiplication(&fai[i], &ciBigInt)
		foldedEvaluations.Add(&foldedEvaluations, &tmp)
	}

	// fold the digests ∑ᵢ[cᵢ]([fᵢ(α)]G₁)
	var foldedDigests Digest
	_, err := foldedDigests.MultiExp(di, ci, ecc.MultiExpConfig{ScalarsMont: true})
	if err != nil {
		return foldedDigests, foldedEvaluations, err
	}

	// folding done
	return foldedDigests, foldedEvaluations, nil

}

// deriveGamma derives a challenge using Fiat Shamir to fold proofs.
func deriveGamma(point fr.Element, digests []Digest, hf hash.Hash) (fr.Element, error) {
	if mpi.SelfRank == 0 {
		// derive the challenge gamma, binded to the point and the commitments
		fs := fiatshamir.NewTranscript(hf, "gamma")
		if err := fs.Bind("gamma", point.Marshal()); err != nil {
			return fr.Element{}, err
		}
		for i := 0; i < len(digests); i++ {
			if err := fs.Bind("gamma", digests[i].Marshal()); err != nil {
				return fr.Element{}, err
			}
		}
		gammaByte, err := fs.ComputeChallenge("gamma")
		if err != nil {
			return fr.Element{}, err
		}
		var gamma fr.Element
		gamma.SetBytes(gammaByte)
		buf := gamma.Bytes()
		for i := 1; i < int(mpi.WorldSize); i++ {
			mpi.SendBytes(buf[:], uint64(i))
		}
		return gamma, nil
	} else {
		buf, err := mpi.ReceiveBytes(32, 0)
		if err != nil {
			return fr.Element{}, err
		}
		var gamma fr.Element
		gamma.SetBytes(buf)
		return gamma, nil
	}
}
