import sympy as sp
from galgebra.ga import Ga

# GAlgebra & SymPy: Null Cone Confinement
sp.init_printing()

# Define the Split-Octonion / Zorn Matrix coordinate space
coords = sp.symbols('a b x1 x2 x3 y1 y2 y3', real=True)
Z = Ga('e_a e_b e_x1 e_x2 e_x3 e_y1 e_y2 e_y3', g=[1, 1, -1, -1, -1, 1, 1, 1], coords=coords)

a, b, x1, x2, x3, y1, y2, y3 = coords

# Zorn Determinant: det(Z) = a*b - x.y
det_Z = a*b - (x1*y1 + x2*y2 + x3*y3)

print("--- Zorn Algebra Null Cone Confinement ---")
print(f"General Determinant: det(Z) = {det_Z}")

# Isolated Quark (x vector only, no anti-color y)
quark_state = {a:0, b:0, y1:0, y2:0, y3:0}
det_quark = det_Z.subs(quark_state)
print(f"Isolated Quark Determinant: det(Q) = {det_quark} -> NULL CONE (Confined)")

# Meson (Quark + Antiquark)
meson_state = {a:0, b:0, x1:1, y1:1, x2:0, y2:0, x3:0, y3:0}
det_meson = det_Z.subs(meson_state)
print(f"Meson Determinant: det(M) = {det_meson} -> BULK (Deconfined/Massive)")
