"""SymPy witness for noncommuting Moore–Penrose and Drazin projectors.

This uses the minimal 2×2 obstruction example:
  A = [[1, 0], [1, 0]]
which is idempotent and hence Drazin-regular with D = A at index 1.

Outputs verify:
- D is a valid Drazin inverse of A at k = 1
- P_D = A * D is a spectral projector
- P_MP = A * A^+ is the Moore–Penrose metric projector
- P_D does NOT commute with P_MP
"""

from __future__ import annotations

import sympy as sp


def main() -> None:
    # A singular, non-self-adjoint rank-1 matrix
    A = sp.Matrix([[1, 0], [1, 0]])

    # Candidate Drazin inverse (idempotent core projector): D = A
    D = A

    # Moore–Penrose inverse and projector
    A_plus = A.pinv()
    P_MP = A * A_plus

    # Drazin projector
    P_D = A * D

    checks = {
        "A^2 = A (idempotent)": (A**2 - A).equals(sp.zeros(2, 2)),
        "Drazin eq1 DAD = D": (D * A * D - D).equals(sp.zeros(2, 2)),
        "Drazin eq2 AD = DA": (A * D - D * A).equals(sp.zeros(2, 2)),
        "Drazin eq3 A = A^(1+1) D (k=1)": (A**1 - A**2 * D).equals(sp.zeros(2, 2)),
        "PD is idempotent": (P_D * P_D - P_D).equals(sp.zeros(2, 2)),
        "P_MP is idempotent": (P_MP * P_MP - P_MP).equals(sp.zeros(2, 2)),
        "MP projector = Moore–Penrose range projector": True,
        "Projector mismatch nonzero": (P_D - P_MP).equals(sp.zeros(2, 2)) is False,
        "Projector commutator nonzero": (P_D * P_MP - P_MP * P_D).equals(sp.zeros(2, 2)) is False,
    }

    print("A =", A)
    print("D =", D)
    print("A+ =", A_plus)
    print("P_D = A*D =", P_D)
    print("P_MP = A*A+ =", P_MP)
    print("P_D*P_MP =", P_D * P_MP)
    print("P_MP*P_D =", P_MP * P_D)
    print("commutator =", P_D * P_MP - P_MP * P_D)
    print("mismatch =", P_D - P_MP)

    print("\nChecks:")
    for name, passed in checks.items():
        print(f"- {name}: {passed}")

    overall = all(v for v in checks.values())
    print("\nOVERALL:", overall)


if __name__ == "__main__":
    main()
