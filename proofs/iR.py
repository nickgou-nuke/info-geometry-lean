import sympy as sp


A = sp.Matrix([[2, -2], [-2, 2]])
delta = sp.Matrix([1, 1])

assert A.det() == 0
assert A.T == A
assert A * delta == sp.zeros(2, 1)
assert sp.gcd(int(delta[0]), int(delta[1])) == 1

print("iR.py: affine A1^(1) imaginary root identities verified")
