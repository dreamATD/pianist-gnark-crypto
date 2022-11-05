package dkzg

import (
	"encoding/binary"
	"io"

	"github.com/consensys/gnark-crypto/ecc/bn254"
)

func uint64ArrayToBytes(a []uint64) []byte {
	b := make([]byte, 8*len(a))
	for i := 0; i < len(a); i++ {
		binary.LittleEndian.PutUint64(b[i*8:], a[i])
	}
	return b
}
func BytesToUint64Array(b []byte) []uint64 {
	a := make([]uint64, len(b)/8)
	for i := 0; i < len(a); i++ {
		a[i] = binary.LittleEndian.Uint64(b[i*8:])
	}
	return a
}

func G1AffineToBytes(p bn254.G1Affine) []byte {
	XBytes := uint64ArrayToBytes(p.X[:])
	YBytes := uint64ArrayToBytes(p.Y[:])
	return append(XBytes, YBytes...)
}

func G1AffineArrayToBytes(a []bn254.G1Affine) []byte {
	b := make([]byte, 0)
	for _, v := range a {
		b = append(b, G1AffineToBytes(v)...)
	}
	return b
}

func BytesToG1Affine(b []byte) bn254.G1Affine {
	var p bn254.G1Affine
	copy(p.X[:], BytesToUint64Array(b[:32]))
	copy(p.Y[:], BytesToUint64Array(b[32:]))
	return p
}

func BytesToG1AffineArray(b []byte) []bn254.G1Affine {
	a := make([]bn254.G1Affine, len(b)/64)
	for i := 0; i < len(a); i++ {
		a[i] = BytesToG1Affine(b[i*64 : (i+1)*64])
	}
	return a
}

func BytesToG2Affine(b []byte) bn254.G2Affine {
	var p bn254.G2Affine
	copy(p.X.A0[:], BytesToUint64Array(b[:32]))
	copy(p.X.A1[:], BytesToUint64Array(b[32:64]))
	copy(p.Y.A0[:], BytesToUint64Array(b[64:96]))
	copy(p.Y.A1[:], BytesToUint64Array(b[96:]))
	return p
}

func BytesToG2AffineArray(b []byte) []bn254.G2Affine {
	a := make([]bn254.G2Affine, len(b)/128)
	for i := 0; i < len(a); i++ {
		a[i] = BytesToG2Affine(b[i*128 : (i+1)*128])
	}
	return a
}

func G2AffineToBytes(p bn254.G2Affine) []byte {
	XA0Bytes := uint64ArrayToBytes(p.X.A0[:])
	XA1Bytes := uint64ArrayToBytes(p.X.A1[:])
	YA0Bytes := uint64ArrayToBytes(p.Y.A0[:])
	YA1Bytes := uint64ArrayToBytes(p.Y.A1[:])
	buf := append(XA0Bytes, XA1Bytes...)
	buf = append(buf, YA0Bytes...)
	buf = append(buf, YA1Bytes...)
	return buf
}

func G2AffineArrayToBytes(a []bn254.G2Affine) []byte {
	b := make([]byte, 0)
	for _, v := range a {
		b = append(b, G2AffineToBytes(v)...)
	}
	return b
}

// WriteTo writes binary encoding of the SRS
func (srs *SRS) WriteTo(w io.Writer) (int64, error) {
	// encode the SRS
	buf := make([]byte, 0)
	buf = append(buf, G2AffineToBytes(srs.G2[0])...)
	buf = append(buf, G2AffineToBytes(srs.G2[1])...)
	buf = append(buf, G1AffineArrayToBytes(srs.G1)...)
	n, err := w.Write(buf)
	return int64(n), err
}

// ReadFrom decodes SRS data from reader.
func (srs *SRS) ReadFrom(r io.Reader) (int64, error) {
	// decode the SRS
	buf := make([]byte, 0)
	buf = append(buf, make([]byte, 128*2)...) // G2
	n, err := r.Read(buf)
	if err != nil {
		return int64(n), err
	}
	// G1
	for {
		subBuf := make([]byte, 64)
		x, err := r.Read(subBuf)
		n += x
		if err != nil {
			if err.Error() == "EOF" {
				break
			}
			return int64(len(buf)), err
		}
		buf = append(buf, subBuf...)
	}
	srs.G2[0] = BytesToG2Affine(buf[:128])
	srs.G2[1] = BytesToG2Affine(buf[128:256])
	srs.G1 = BytesToG1AffineArray(buf[256:])
	return int64(n), nil
}
