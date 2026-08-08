"""SymPy witness: K-theory of the Fibonacci Cuntz--Krieger algebra.

For the Fibonacci adjacency matrix

    A = [[1,1],[1,0]],

Cuntz--Krieger K-theory is

    K0(O_A) = coker(I - A^T),
    K1(O_A) = ker(I - A^T).

Here I-A^T has determinant -1, hence is unimodular over Z. Therefore it is an
integer automorphism of Z^2, so both coker and kernel are trivial.
"""

import sympy as sp

A = sp.Matrix([[1, 1], [1, 0]])
B = sp.eye(2) - A.T
C = B.inv()

print("§1  Fibonacci Cuntz--Krieger matrix")
print("A =")
sp.pprint(A)
print("I - A.T =")
sp.pprint(B)

print("§2  Unimodularity")
detB = int(B.det())
assert detB == -1
assert all(x == int(x) for x in C)
assert B * C == sp.eye(2)
assert C * B == sp.eye(2)
print("   det(I-Aᵀ)=-1 and inverse is integral ✓")

print("§3  K-groups")
# Smith normal form invariants are both 1 for a unimodular 2x2 integer matrix.
# Thus coker(B)=Z/1⊕Z/1=0 and ker(B)=0.
rank = B.rank()
assert rank == 2
print("   K0(O_A)=coker(I-Aᵀ)=0 ✓")
print("   K1(O_A)=ker(I-Aᵀ)=0 ✓")

print()
print("cuntz_krieger_fibonacci_k.py: All identities verified")
