// Copyright 2020 ConsenSys AG
//
// Licensed under the Apache License, Version 2.0 (the "License");
// you may not use this file except in compliance with the License.
// You may obtain a copy of the License at
//
//     http://www.apache.org/licenses/LICENSE-2.0
//
// Unless required by applicable law or agreed to in writing, software
// distributed under the License is distributed on an "AS IS" BASIS,
// WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
// See the License for the specific language governing permissions and
// limitations under the License.

package bn256

import (
	"math/big"

	"github.com/consensys/gurvy/bn256/fp"
	"github.com/consensys/gurvy/bn256/internal/fptower"
	"github.com/consensys/gurvy/utils"
)

// hashToFp hashes msg to count prime field elements.
// https://tools.ietf.org/html/draft-irtf-cfrg-hash-to-curve-06#section-5.2
func hashToFp(msg, dst []byte, count int) ([]fp.Element, error) {

	// 128 bits of security
	// L = ceil((ceil(log2(p)) + k) / 8), where k is the security parameter = 128
	L := 48

	lenInBytes := count * L
	pseudoRandomBytes, err := utils.ExpandMsgXmd(msg, dst, lenInBytes)
	if err != nil {
		return nil, err
	}

	res := make([]fp.Element, count)
	for i := 0; i < count; i++ {
		res[i].SetBytes(pseudoRandomBytes[i*L : (i+1)*L])
	}
	return res, nil
}

// returns false if u>-u when seen as a bigInt
func sign0(u fp.Element) bool {
	var a, b big.Int
	u.ToBigIntRegular(&a)
	u.Neg(&u)
	u.ToBigIntRegular(&b)
	return a.Cmp(&b) <= 0
}

// ----------------------------------------------------------------------------------------
// G1

// https://tools.ietf.org/html/draft-irtf-cfrg-hash-to-curve-06#section-4.1
// Shallue and van de Woestijne method, works for any elliptic curve in Weierstrass curve
func svdwMapG1(u fp.Element) G1 {

	var twoInv, tmp fp.Element
	var res G1

	// constants
	// sage script to find z: https://tools.ietf.org/html/draft-irtf-cfrg-hash-to-curve-06#appendix-E.1
	var z, c1, c2, c3, c4 fp.Element
	z.SetOne()
	c1.Square(&z).Mul(&c1, &z).Add(&c1, &bCurveCoeff)
	twoInv.SetUint64(2).Inverse(&twoInv)
	c2.Neg(&z).Mul(&c2, &twoInv)
	tmp.Square(&z)
	c3.Double(&tmp).Add(&c3, &tmp).Mul(&c3, &c1).Neg(&c3).Sqrt(&c3) // sgn0(c3) MUST equal 1
	if !sign0(c3) {
		c3.Neg(&c3)
	}
	c4.Double(&tmp).Add(&c4, &tmp).Inverse(&c4).Mul(&c4, &c1).Double(&c4).Double(&c4)

	var tv1, tv2, tv3, tv4, one, x1, gx1, x2, gx2, x3, x, gx, y fp.Element
	one.SetOne()
	tv1.Square(&u).Mul(&tv1, &c1)
	tv2.Add(&one, &tv1)
	tv1.Sub(&one, &tv1)
	tv3.Mul(&tv2, &tv1).Inverse(&tv3)
	tv4.Mul(&u, &tv1)
	tv4.Mul(&tv4, &tv3)
	tv4.Mul(&tv4, &c3)
	x1.Sub(&c2, &tv4)
	gx1.Square(&x1)
	// 12. gx1 = gx1 + A
	gx1.Mul(&gx1, &x1)
	gx1.Add(&gx1, &bCurveCoeff)
	e1 := gx1.Legendre()
	x2.Add(&c2, &tv4)
	gx2.Square(&x2)
	// 18. gx2 = gx2 + A
	gx2.Mul(&gx2, &x2)
	gx2.Add(&gx2, &bCurveCoeff)
	e2 := gx2.Legendre() - e1 // 2 if is_square(gx2) AND NOT e1
	x3.Square(&tv2)
	x3.Mul(&x3, &tv3)
	x3.Square(&x3)
	x3.Mul(&x3, &c4)
	x3.Add(&x3, &z)
	if e1 == 1 {
		x.Set(&x1)
	} else {
		x.Set(&x3)
	}
	if e2 == 2 {
		x.Set(&x2)
	}
	gx.Square(&x)
	// gx = gx + A
	gx.Mul(&gx, &x)
	gx.Add(&gx, &bCurveCoeff)
	y.Sqrt(&gx)
	e3 := sign0(u) && sign0(y)
	if !e3 {
		y.Neg(&y)
	}
	res.X.Set(&x)
	res.Y.Set(&y)

	return res
}

// MapToCurveG1Svdw maps an fp.Element to a point on the curve using the Shallue and van de Woestijne map
// https://tools.ietf.org/html/draft-irtf-cfrg-hash-to-curve-06#section-2.2.1
func MapToCurveG1Svdw(t fp.Element) G1 {
	res := svdwMapG1(t)
	return res
}

// EncodeToCurveG1Svdw maps an fp.Element to a point on the curve using the Shallue and van de Woestijne map
// https://tools.ietf.org/html/draft-irtf-cfrg-hash-to-curve-06#section-2.2.2
func EncodeToCurveG1Svdw(msg, dst []byte) (G1, error) {
	var res G1
	t, err := hashToFp(msg, dst, 1)
	if err != nil {
		return res, err
	}
	res = MapToCurveG1Svdw(t[0])
	return res, nil
}

// HashToCurveG1Svdw maps an fp.Element to a point on the curve using the Shallue and van de Woestijne map
// https://tools.ietf.org/html/draft-irtf-cfrg-hash-to-curve-06#section-3
func HashToCurveG1Svdw(msg, dst []byte) (G1, error) {
	var res G1
	u, err := hashToFp(msg, dst, 2)
	if err != nil {
		return res, err
	}
	Q0 := MapToCurveG1Svdw(u[0])
	Q1 := MapToCurveG1Svdw(u[1])
	var _Q0, _Q1, _res G1Jac
	_Q0.FromAffine(&Q0)
	_Q1.FromAffine(&Q1)
	_res.Set(&_Q1).AddAssign(&_Q0)
	res.FromJacobian(&_res)
	return res, nil
}

// ----------------------------------------------------------------------------------------
// G2

// https://tools.ietf.org/html/draft-irtf-cfrg-hash-to-curve-06#section-4.1
// Shallue and van de Woestijne method, works for any elliptic curve in Weierstrass curve
func svdwMapG2(u fptower.E2) G2 {

	var twoInv fp.Element
	var tmp fptower.E2
	var res G2

	// constants
	// sage script to find z: https://tools.ietf.org/html/draft-irtf-cfrg-hash-to-curve-06#appendix-E.1
	var z, c1, c2, c3, c4 fptower.E2
	z.A1.SetString("1")
	c1.Square(&z).Mul(&c1, &z).Add(&c1, &bTwistCurveCoeff)
	twoInv.SetUint64(2).Inverse(&twoInv)
	c2.Neg(&z).MulByElement(&c2, &twoInv)
	tmp.Square(&z)
	c3.Double(&tmp).Add(&c3, &tmp).Mul(&c3, &c1).Neg(&c3).Sqrt(&c3) // sgn0(c3) MUST equal 1
	// TODO find norms for which sqrt to take for fp2 elements
	if !sign0(c3.A0) {
		c3.Neg(&c3)
	}
	c4.Double(&tmp).Add(&c4, &tmp).Inverse(&c4).Mul(&c4, &c1).Double(&c4).Double(&c4)

	var tv1, tv2, tv3, tv4, one, x1, gx1, x2, gx2, x3, x, gx, y fptower.E2
	one.SetOne()
	tv1.Square(&u).Mul(&tv1, &c1)
	tv2.Add(&one, &tv1)
	tv1.Sub(&one, &tv1)
	tv3.Mul(&tv2, &tv1).Inverse(&tv3)
	tv4.Mul(&u, &tv1)
	tv4.Mul(&tv4, &tv3)
	tv4.Mul(&tv4, &c3)
	x1.Sub(&c2, &tv4)
	gx1.Square(&x1)
	// 12. gx1 = gx1 + A
	gx1.Mul(&gx1, &x1)
	gx1.Add(&gx1, &bTwistCurveCoeff)
	e1 := gx1.Legendre()
	x2.Add(&c2, &tv4)
	gx2.Square(&x2)
	// 18. gx2 = gx2 + A
	gx2.Mul(&gx2, &x2)
	gx2.Add(&gx2, &bTwistCurveCoeff)
	e2 := gx2.Legendre() - e1 // 2 if is_square(gx2) AND NOT e1
	x3.Square(&tv2)
	x3.Mul(&x3, &tv3)
	x3.Square(&x3)
	x3.Mul(&x3, &c4)
	x3.Add(&x3, &z)
	if e1 == 1 {
		x.Set(&x1)
	} else {
		x.Set(&x3)
	}
	if e2 == 2 {
		x.Set(&x2)
	}
	gx.Square(&x)
	// gx = gx + A
	gx.Mul(&gx, &x)
	gx.Add(&gx, &bTwistCurveCoeff)
	y.Sqrt(&gx)
	e3 := sign0(u.A0) && sign0(y.A0)
	if !e3 {
		y.Neg(&y)
	}
	res.X.Set(&x)
	res.Y.Set(&y)

	return res
}

// MapToCurveG2Svdw maps an fp.Element to a point on the curve using the Shallue and van de Woestijne map
// https://tools.ietf.org/html/draft-irtf-cfrg-hash-to-curve-06#section-2.2.1
func MapToCurveG2Svdw(t fptower.E2) G2 {
	res := svdwMapG2(t)
	res.ClearCofactor(&res)
	return res
}

// EncodeToCurveG2Svdw maps an fp.Element to a point on the curve using the Shallue and van de Woestijne map
// https://tools.ietf.org/html/draft-irtf-cfrg-hash-to-curve-06#section-2.2.2
func EncodeToCurveG2Svdw(msg, dst []byte) (G2, error) {
	var res G2
	_t, err := hashToFp(msg, dst, 2)
	if err != nil {
		return res, err
	}
	var t fptower.E2
	t.A0.Set(&_t[0])
	t.A1.Set(&_t[1])
	res = MapToCurveG2Svdw(t)
	return res, nil
}

// HashToCurveG2Svdw maps an fp.Element to a point on the curve using the Shallue and van de Woestijne map
// https://tools.ietf.org/html/draft-irtf-cfrg-hash-to-curve-06#section-3
func HashToCurveG2Svdw(msg, dst []byte) (G2, error) {
	var res G2
	u, err := hashToFp(msg, dst, 4)
	if err != nil {
		return res, err
	}
	var u0, u1 fptower.E2
	u0.A0.Set(&u[0])
	u0.A1.Set(&u[1])
	u1.A0.Set(&u[2])
	u1.A1.Set(&u[3])
	Q0 := MapToCurveG2Svdw(u0)
	Q1 := MapToCurveG2Svdw(u1)
	var _Q0, _Q1, _res G2Jac
	_Q0.FromAffine(&Q0)
	_Q1.FromAffine(&Q1)
	_res.Set(&_Q1).AddAssign(&_Q0)
	res.FromJacobian(&_res)
	return res, nil
}
