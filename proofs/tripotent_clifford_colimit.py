"""SymPy witness: tripotent trifactor geometry survives Clifford scale embeddings.

Checks:
- split-octonion sign sectors: compact (-), split (+), null (0);
- tripotent scale operator T=diag(1,-1,0), T^3=T;
- Clifford/CAR scale inclusion modeled by T |-> T ⊗ I_2 preserves tripotency;
- eigenspace multiplicities for {+1,-1,0} double under one inclusion;
- after n inclusions, T ⊗ I_{2^n} remains tripotent with all three sectors present.
"""

import sympy as sp

print("§1  Split-octonion Cartan/sign sectors")
n = sp.symbols("n", integer=True, nonnegative=True)
# Convention: quaternionic imaginary units square to -1; split units square to +1.
square_sign = {f"e{i}": -1 for i in range(1, 4)}
square_sign.update({f"e{i}": 1 for i in range(4, 8)})
assert [square_sign[f"e{i}"] for i in range(1, 4)] == [-1, -1, -1]
assert [square_sign[f"e{i}"] for i in range(4, 8)] == [1, 1, 1, 1]
# Split (4,4) null vector.
x = sp.symbols("x0:8")
split_norm = sum(x[i]**2 for i in range(4)) - sum(x[i]**2 for i in range(4, 8))
assert split_norm.subs({x[0]: 1, x[4]: 1, **{x[i]: 0 for i in [1,2,3,5,6,7]}}) == 0
print("   compact e1,e2,e3 square -1; split e4..e7 square +1; null cone nonempty ✓")

print("§2  Tripotent trifactor operator")
T = sp.diag(1, -1, 0)
assert T**3 == T
assert sp.factor((sp.symbols('s')*sp.eye(3)-T).det()) == sp.symbols('s')*(sp.symbols('s')-1)*(sp.symbols('s')+1)
print("   T=diag(1,-1,0), T³=T, poles {-1,0,+1} ✓")

print("§3  Clifford inclusion T -> T ⊗ I₂ preserves tripotency")
I2 = sp.eye(2)
T1 = sp.kronecker_product(T, I2)
assert T1**3 == T1
assert T1.eigenvals() == {sp.Integer(1): 2, sp.Integer(-1): 2, sp.Integer(0): 2}
print("   one scale step doubles every sector and preserves T³=T ✓")

print("§4  Finite inductive tower")
for m in range(5):
    Tm = sp.kronecker_product(T, sp.eye(2**m))
    assert Tm**3 == Tm
    ev = Tm.eigenvals()
    assert ev[sp.Integer(1)] == 2**m
    assert ev[sp.Integer(-1)] == 2**m
    assert ev[sp.Integer(0)] == 2**m
print("   T ⊗ I_{2^n} keeps boson/fermion/zero-mode sectors for n≤4 ✓")

print()
print("tripotent_clifford_colimit.py: All identities verified")
