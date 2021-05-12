// Copyright 2020 ConsenSys Software Inc.
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

// Code generated by consensys/gnark-crypto DO NOT EDIT

package kzg

import (
	"math/bits"

	"github.com/consensys/gnark-crypto/ecc/bls12-381/fr"
	"github.com/consensys/gnark-crypto/ecc/bls12-381/fr/fft"
	bls12381_pol "github.com/consensys/gnark-crypto/ecc/bls12-381/fr/polynomial"
)

// dividePolyByXminusA computes (f-f(a))/(x-a), in canonical basis, in regular form
func dividePolyByXminusA(d fft.Domain, f bls12381_pol.Polynomial, fa, a fr.Element) bls12381_pol.Polynomial {

	// padd f so it has size d.Cardinality
	_f := make([]fr.Element, d.Cardinality)
	copy(_f, f)

	// compute the quotient (f-f(a))/(x-a)
	d.FFT(_f, fft.DIF, 0)

	// bit reverse shift
	bShift := uint64(64 - bits.TrailingZeros64(d.Cardinality))

	accumulator := fr.One()

	s := make([]fr.Element, len(_f))
	for i := 0; i < len(s); i++ {
		irev := bits.Reverse64(uint64(i)) >> bShift
		s[irev].Sub(&accumulator, &a)
		accumulator.Mul(&accumulator, &d.Generator)
	}
	s = fr.BatchInvert(s)

	for i := 0; i < len(_f); i++ {
		_f[i].Sub(&_f[i], &fa)
		_f[i].Mul(&_f[i], &s[i])
	}

	d.FFTInverse(_f, fft.DIT, 0)

	// the result is of degree deg(f)-1
	return _f[:len(f)-1]
}
