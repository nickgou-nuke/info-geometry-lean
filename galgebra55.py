"""
Cl(5,5) and O(5,5) implementation using galgebra (SymPy-based).
"""

import sympy
from galgebra.ga import Ga
import numpy as np


class Clifford55SymPy:
    """Cl(5,5) using galgebra (SymPy-based)."""

    def __init__(self):
        self.ga = Ga(
            'e1 e2 e3 e4 e5 e6 e7 e8 e9 e10',
            g=[1, 1, 1, 1, 1, -1, -1, -1, -1, -1]
        )
        self.e = list(self.ga.mv_basis)
        self._build_bivector_basis()
        self._build_d4_roots()

    def _build_bivector_basis(self):
        self.bivectors = []
        self.bivector_labels = []
        for i in range(10):
            for j in range(i+1, 10):
                B = self.e[i] ^ self.e[j]
                self.bivectors.append(B)
                self.bivector_labels.append(f'e{i+1}^e{j+1}')
        assert len(self.bivectors) == 45

    def _build_d4_roots(self):
        self.d4_roots = []
        self.d4_root_labels = []
        for i in range(4):
            for j in range(i+1, 4):
                for si in [1, -1]:
                    for sj in [1, -1]:
                        r = si * self.e[i] + sj * self.e[j]
                        self.d4_roots.append(r)
                        label = f"{'+' if si>0 else '-'}{i+1}{'+' if sj>0 else '-'}{j+1}"
                        self.d4_root_labels.append(label)
        assert len(self.d4_roots) == 24

    def commutator(self, A, B):
        return A * B - B * A

    def pseudoscalar(self):
        ps = self.e[0]
        for ei in self.e[1:]:
            ps = ps * ei
        return ps

    def verify(self):
        print("=== galgebra Cl(5,5) Verification ===")
        print(f"Metric: {self.ga.g}")

        print("\nBivector squares (first 6):")
        for B, label in zip(self.bivectors[:6], self.bivector_labels[:6]):
            sq = B * B
            print(f"  {label}^2 = {sq}")

        print(f"\nD4 root count: {len(self.d4_roots)}")
        for r, label in zip(self.d4_roots[:4], self.d4_root_labels[:4]):
            r_sq = r * r
            print(f"  {label}^2 = {r_sq}")

        B12 = self.bivectors[0]
        B13 = self.bivectors[1]
        comm = self.commutator(B12, B13)
        print(f"\n[e1^e2, e1^e3] = {comm}")

        ps = self.pseudoscalar()
        ps_sq = ps * ps
        print(f"\nPseudoscalar^2 = {ps_sq}")

        print("\nDone.")


def main():
    print("=" * 60)
    print("Cl(5,5) and O(5,5) via galgebra (SymPy)")
    print("=" * 60)
    cl = Clifford55SymPy()
    cl.verify()


if __name__ == '__main__':
    main()
