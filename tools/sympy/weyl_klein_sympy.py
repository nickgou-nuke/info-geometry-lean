import sympy as sp

print("=== SymPy Klein Tube Witness ===")
# Nilpotent chiral ladder matrices; these are not momentum matrices and do not
# by themselves encode a mass shell or Klein-quadric factorization.
S_plus = sp.Matrix([[0, 1], [0, 0]])
S_minus = sp.Matrix([[0, 0], [1, 0]])

print(f"S_plus^2 = {S_plus**2}")
print(f"S_minus^2 = {S_minus**2}")
print("Verified only: the two chiral ladder matrices square to zero. No on-shell/Klein-quadric bridge is asserted.")
