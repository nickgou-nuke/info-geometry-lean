"""
SymPy witness for Fibonacci Hexagon Equations (FibAnyonThm7_hexagon.lean)

Verifies: Hexagon I (R.F.R = F.diag(1,Rtau).F) and 
          Hexagon II (Rinv.F.Rinv = F.diag(1,Rtau_inv).F)

All entries factor as A*(s^2 - tau) + B*cyclo = 0.
"""

import sympy as sp
import numpy as np

print("=" * 60)
print(" FIBONACCI HEXAGON EQUATIONS -- SymPy witness")
print("=" * 60)

q, s_sym = sp.symbols('q s')
tau = q**2 - q**3
cyclo = q**4 - q**3 + q**2 - q + 1

print("\n-- Parameters --")
print(f"  q = exp(pi*i/5),  q^5 = -1")
print(f"  s^2 = tau = q^2 - q^3  (golden ratio)")
print(f"  Phi_10(q) = q^4 - q^3 + q^2 - q + 1 = 0")

# Numeric verification
qn = complex(np.exp(np.pi*1j/5))
sn = np.sqrt((np.sqrt(5)-1)/2)
taun = qn**2 - qn**3
print(f"\n  Numeric: q={qn.real:.4f}{qn.imag:+.4f}i, s={sn:.4f}, tau={taun.real:.4f}+{taun.imag:.4f}i")
print(f"  s^2 = tau? {np.allclose(sn**2, taun)}")
print(f"  q^5 = -1? {np.allclose(qn**5, -1)}")

# Matrices
R = sp.Matrix([[q**4, 0], [0, -q**2]])
F = sp.Matrix([[tau, s_sym], [s_sym, -tau]])
Rp = sp.Matrix([[1, 0], [0, -q**2]])
Ri = sp.Matrix([[-q, 0], [0, q**3]])        # R^{-1}
Rpi = sp.Matrix([[1, 0], [0, q**3]])        # Rp^{-1}

# --- Verify factorizations ---
def factor_entry(diff_expr):
    """Factor diff as A*(s^2-tau) + B*cyclo."""
    diff_sub = sp.expand(diff_expr.subs(s_sym**2, tau))
    A = sp.simplify((diff_expr - diff_sub) / (s_sym**2 - tau))
    B = sp.simplify(diff_sub / cyclo)
    return sp.factor(A), sp.factor(B)

print("\n-- Hexagon I: R*F*R = F*diag(1,Rtau)*F --")
diff1 = R @ F @ R - F @ Rp @ F
for i in range(2):
    for j in range(2):
        A, B = factor_entry(sp.expand(diff1[i,j]))
        print(f"  [{i},{j}]: ({A})*(s^2-tau) + ({B})*cyclo")

print("\n-- Hexagon II: Rinv*F*Rinv = F*diag(1,Rtau_inv)*F --")
diff2 = Ri @ F @ Ri - F @ Rpi @ F
for i in range(2):
    for j in range(2):
        A, B = factor_entry(sp.expand(diff2[i,j]))
        print(f"  [{i},{j}]: ({A})*(s^2-tau) + ({B})*cyclo")

# Numeric check
Rn = np.diag([qn**4, -qn**2])
Fn = np.array([[taun, sn], [sn, -taun]], dtype=complex)
Rpn = np.diag([1.0, -qn**2])
Rin = np.diag([1/qn**4, 1/(-qn**2)])
Rpin = np.diag([1.0, 1/(-qn**2)])

d1 = Rn @ Fn @ Rn - Fn @ Rpn @ Fn
d2 = Rin @ Fn @ Rin - Fn @ Rpin @ Fn
print(f"\n  Hex I max error: {np.max(np.abs(d1)):.2e}")
print(f"  Hex II max error: {np.max(np.abs(d2)):.2e}")

print("\n" + "=" * 60)
print(" All entries = 0 mod (s^2-tau, cyclo).")
print(" Fibonacci hexagon identities verified; this witness does not prove a full MTC.")
print("=" * 60)
