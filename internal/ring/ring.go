package ring

type Ring int

const (
	Z2 Ring = 2
	Z3 Ring = 3
)

func (r Ring) Normalize(x int) int {
	modulus := r.modulus()
	x %= modulus
	if x < 0 {
		x += modulus
	}
	return x
}

func (r Ring) Add(a, b int) int {
	return r.Normalize(r.Normalize(a) + r.Normalize(b))
}

func (r Ring) Sub(a, b int) int {
	return r.Normalize(r.Normalize(a) - r.Normalize(b))
}

func (r Ring) Mul(a, b int) int {
	return r.Normalize(r.Normalize(a) * r.Normalize(b))
}

func (r Ring) modulus() int {
	switch r {
	case Z2, Z3:
		return int(r)
	default:
		panic("unsupported ring")
	}
}
