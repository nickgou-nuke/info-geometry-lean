"""Matrix checks for associative commutator Lie identities."""
import sympy as sp

print("§1 commutator Jacobi identity")

def comm(x, y):
    return x*y - y*x

def anti(x, y):
    return x*y + y*x

x = sp.Matrix([[1, 2], [3, 4]])
y = sp.Matrix([[0, 5], [7, 1]])
z = sp.Matrix([[2, -1], [4, 3]])
assert comm(x, comm(y, z)) + comm(y, comm(z, x)) + comm(z, comm(x, y)) == sp.zeros(2)
print("   [x,[y,z]]+[y,[z,x]]+[z,[x,y]]=0 ✓")

print("§2 derivation identities")
assert comm(x, y*z) == comm(x, y)*z + y*comm(x, z)
assert comm(x*y, z) == x*comm(y, z) + comm(x, z)*y
print("   [x,yz]=[x,y]z+y[x,z] and [xy,z]=x[y,z]+[x,z]y ✓")

print("§3 operator central charge")
lam = sp.symbols("lam")
Z = lam * sp.eye(2)
assert comm(Z, x) == sp.zeros(2)
assert comm(Z*x, y) == Z*comm(x, y)
assert comm(x*Z, y) == Z*comm(x, y)
print("   central operator Z commutes and factors out of commutators ✓")

print("§4 nilpotent chiral square")
Qp = sp.Matrix([[0, 1], [0, 0]])
Qm = sp.Matrix([[0, 0], [1, 0]])
assert Qp*Qp == sp.zeros(2)
assert Qm*Qm == sp.zeros(2)
assert (Qp + Qm)*(Qp + Qm) == anti(Qp, Qm)
print("   Q±²=0 => (Q+ + Q-)²={Q+,Q-} ✓")

print("associative_commutator_lie.py: all identities verified")
