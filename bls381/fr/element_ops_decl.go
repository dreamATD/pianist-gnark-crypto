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

// Code generated by goff (v0.3.1) DO NOT EDIT

// Package fr contains field arithmetic operations
package fr

import "math/bits"

// -------------------------------------------------------------------------------------------------
// Declarations

//go:noescape
func add(res, x, y *Element)

//go:noescape
func sub(res, x, y *Element)

//go:noescape
func neg(res, x *Element)

//go:noescape
func double(res, x *Element)

//go:noescape
func mul(res, x, y *Element)

//go:noescape
func square(res, x *Element)

//go:noescape
func fromMont(res *Element)

//go:noescape
func reduce(res *Element)

// E2

// Generic (no ADX instructions, no AMD64) versions

func _mulGeneric(z, x, y *Element) {

	var t [4]uint64
	var c [3]uint64
	{
		// round 0
		v := x[0]
		c[1], c[0] = bits.Mul64(v, y[0])
		m := c[0] * 18446744069414584319
		c[2] = madd0(m, 18446744069414584321, c[0])
		c[1], c[0] = madd1(v, y[1], c[1])
		c[2], t[0] = madd2(m, 6034159408538082302, c[2], c[0])
		c[1], c[0] = madd1(v, y[2], c[1])
		c[2], t[1] = madd2(m, 3691218898639771653, c[2], c[0])
		c[1], c[0] = madd1(v, y[3], c[1])
		t[3], t[2] = madd3(m, 8353516859464449352, c[0], c[2], c[1])
	}
	{
		// round 1
		v := x[1]
		c[1], c[0] = madd1(v, y[0], t[0])
		m := c[0] * 18446744069414584319
		c[2] = madd0(m, 18446744069414584321, c[0])
		c[1], c[0] = madd2(v, y[1], c[1], t[1])
		c[2], t[0] = madd2(m, 6034159408538082302, c[2], c[0])
		c[1], c[0] = madd2(v, y[2], c[1], t[2])
		c[2], t[1] = madd2(m, 3691218898639771653, c[2], c[0])
		c[1], c[0] = madd2(v, y[3], c[1], t[3])
		t[3], t[2] = madd3(m, 8353516859464449352, c[0], c[2], c[1])
	}
	{
		// round 2
		v := x[2]
		c[1], c[0] = madd1(v, y[0], t[0])
		m := c[0] * 18446744069414584319
		c[2] = madd0(m, 18446744069414584321, c[0])
		c[1], c[0] = madd2(v, y[1], c[1], t[1])
		c[2], t[0] = madd2(m, 6034159408538082302, c[2], c[0])
		c[1], c[0] = madd2(v, y[2], c[1], t[2])
		c[2], t[1] = madd2(m, 3691218898639771653, c[2], c[0])
		c[1], c[0] = madd2(v, y[3], c[1], t[3])
		t[3], t[2] = madd3(m, 8353516859464449352, c[0], c[2], c[1])
	}
	{
		// round 3
		v := x[3]
		c[1], c[0] = madd1(v, y[0], t[0])
		m := c[0] * 18446744069414584319
		c[2] = madd0(m, 18446744069414584321, c[0])
		c[1], c[0] = madd2(v, y[1], c[1], t[1])
		c[2], z[0] = madd2(m, 6034159408538082302, c[2], c[0])
		c[1], c[0] = madd2(v, y[2], c[1], t[2])
		c[2], z[1] = madd2(m, 3691218898639771653, c[2], c[0])
		c[1], c[0] = madd2(v, y[3], c[1], t[3])
		z[3], z[2] = madd3(m, 8353516859464449352, c[0], c[2], c[1])
	}

	// if z > q --> z -= q
	// note: this is NOT constant time
	if !(z[3] < 8353516859464449352 || (z[3] == 8353516859464449352 && (z[2] < 3691218898639771653 || (z[2] == 3691218898639771653 && (z[1] < 6034159408538082302 || (z[1] == 6034159408538082302 && (z[0] < 18446744069414584321))))))) {
		var b uint64
		z[0], b = bits.Sub64(z[0], 18446744069414584321, 0)
		z[1], b = bits.Sub64(z[1], 6034159408538082302, b)
		z[2], b = bits.Sub64(z[2], 3691218898639771653, b)
		z[3], _ = bits.Sub64(z[3], 8353516859464449352, b)
	}
}

func _squareGeneric(z, x *Element) {

	var t [4]uint64
	var c [3]uint64
	{
		// round 0
		v := x[0]
		c[1], c[0] = bits.Mul64(v, x[0])
		m := c[0] * 18446744069414584319
		c[2] = madd0(m, 18446744069414584321, c[0])
		c[1], c[0] = madd1(v, x[1], c[1])
		c[2], t[0] = madd2(m, 6034159408538082302, c[2], c[0])
		c[1], c[0] = madd1(v, x[2], c[1])
		c[2], t[1] = madd2(m, 3691218898639771653, c[2], c[0])
		c[1], c[0] = madd1(v, x[3], c[1])
		t[3], t[2] = madd3(m, 8353516859464449352, c[0], c[2], c[1])
	}
	{
		// round 1
		v := x[1]
		c[1], c[0] = madd1(v, x[0], t[0])
		m := c[0] * 18446744069414584319
		c[2] = madd0(m, 18446744069414584321, c[0])
		c[1], c[0] = madd2(v, x[1], c[1], t[1])
		c[2], t[0] = madd2(m, 6034159408538082302, c[2], c[0])
		c[1], c[0] = madd2(v, x[2], c[1], t[2])
		c[2], t[1] = madd2(m, 3691218898639771653, c[2], c[0])
		c[1], c[0] = madd2(v, x[3], c[1], t[3])
		t[3], t[2] = madd3(m, 8353516859464449352, c[0], c[2], c[1])
	}
	{
		// round 2
		v := x[2]
		c[1], c[0] = madd1(v, x[0], t[0])
		m := c[0] * 18446744069414584319
		c[2] = madd0(m, 18446744069414584321, c[0])
		c[1], c[0] = madd2(v, x[1], c[1], t[1])
		c[2], t[0] = madd2(m, 6034159408538082302, c[2], c[0])
		c[1], c[0] = madd2(v, x[2], c[1], t[2])
		c[2], t[1] = madd2(m, 3691218898639771653, c[2], c[0])
		c[1], c[0] = madd2(v, x[3], c[1], t[3])
		t[3], t[2] = madd3(m, 8353516859464449352, c[0], c[2], c[1])
	}
	{
		// round 3
		v := x[3]
		c[1], c[0] = madd1(v, x[0], t[0])
		m := c[0] * 18446744069414584319
		c[2] = madd0(m, 18446744069414584321, c[0])
		c[1], c[0] = madd2(v, x[1], c[1], t[1])
		c[2], z[0] = madd2(m, 6034159408538082302, c[2], c[0])
		c[1], c[0] = madd2(v, x[2], c[1], t[2])
		c[2], z[1] = madd2(m, 3691218898639771653, c[2], c[0])
		c[1], c[0] = madd2(v, x[3], c[1], t[3])
		z[3], z[2] = madd3(m, 8353516859464449352, c[0], c[2], c[1])
	}

	// if z > q --> z -= q
	// note: this is NOT constant time
	if !(z[3] < 8353516859464449352 || (z[3] == 8353516859464449352 && (z[2] < 3691218898639771653 || (z[2] == 3691218898639771653 && (z[1] < 6034159408538082302 || (z[1] == 6034159408538082302 && (z[0] < 18446744069414584321))))))) {
		var b uint64
		z[0], b = bits.Sub64(z[0], 18446744069414584321, 0)
		z[1], b = bits.Sub64(z[1], 6034159408538082302, b)
		z[2], b = bits.Sub64(z[2], 3691218898639771653, b)
		z[3], _ = bits.Sub64(z[3], 8353516859464449352, b)
	}
}

func _fromMontGeneric(z *Element) {
	// the following lines implement z = z * 1
	// with a modified CIOS montgomery multiplication
	{
		// m = z[0]n'[0] mod W
		m := z[0] * 18446744069414584319
		C := madd0(m, 18446744069414584321, z[0])
		C, z[0] = madd2(m, 6034159408538082302, z[1], C)
		C, z[1] = madd2(m, 3691218898639771653, z[2], C)
		C, z[2] = madd2(m, 8353516859464449352, z[3], C)
		z[3] = C
	}
	{
		// m = z[0]n'[0] mod W
		m := z[0] * 18446744069414584319
		C := madd0(m, 18446744069414584321, z[0])
		C, z[0] = madd2(m, 6034159408538082302, z[1], C)
		C, z[1] = madd2(m, 3691218898639771653, z[2], C)
		C, z[2] = madd2(m, 8353516859464449352, z[3], C)
		z[3] = C
	}
	{
		// m = z[0]n'[0] mod W
		m := z[0] * 18446744069414584319
		C := madd0(m, 18446744069414584321, z[0])
		C, z[0] = madd2(m, 6034159408538082302, z[1], C)
		C, z[1] = madd2(m, 3691218898639771653, z[2], C)
		C, z[2] = madd2(m, 8353516859464449352, z[3], C)
		z[3] = C
	}
	{
		// m = z[0]n'[0] mod W
		m := z[0] * 18446744069414584319
		C := madd0(m, 18446744069414584321, z[0])
		C, z[0] = madd2(m, 6034159408538082302, z[1], C)
		C, z[1] = madd2(m, 3691218898639771653, z[2], C)
		C, z[2] = madd2(m, 8353516859464449352, z[3], C)
		z[3] = C
	}

	// if z > q --> z -= q
	// note: this is NOT constant time
	if !(z[3] < 8353516859464449352 || (z[3] == 8353516859464449352 && (z[2] < 3691218898639771653 || (z[2] == 3691218898639771653 && (z[1] < 6034159408538082302 || (z[1] == 6034159408538082302 && (z[0] < 18446744069414584321))))))) {
		var b uint64
		z[0], b = bits.Sub64(z[0], 18446744069414584321, 0)
		z[1], b = bits.Sub64(z[1], 6034159408538082302, b)
		z[2], b = bits.Sub64(z[2], 3691218898639771653, b)
		z[3], _ = bits.Sub64(z[3], 8353516859464449352, b)
	}
}
