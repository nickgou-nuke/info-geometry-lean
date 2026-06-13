"""
Cl(5,5) and O(5,5) implementation using clifford.

Provides:
1. Cl(5,5) Clifford algebra with full multivector arithmetic
2. so(5,5) Lie algebra generators (45 bivectors)
3. The 24 D4 root system embedded in Cl(5,5)
4. O(5,5) rotor representations
5. Certificate generation for Lean bridge consumption
"""

import clifford
import numpy as np
from typing import List, Tuple, Dict
from functools import lru_cache


class Clifford55:
    """Cl(5,5) Clifford algebra wrapper."""

    def __init__(self):
        self.layout, self.blades = clifford.Cl(5, 5)
        self.e = [self.blades[f'e{i}'] for i in range(1, 11)]
        self._build_bivector_basis()
        self._build_d4_roots()
        self._build_blade_index_map()

    def _build_blade_index_map(self):
        """Build mapping from blade bitmaps to array indices."""
        self._bitmap_to_idx = {}
        for idx, blade_tuple in enumerate(self.layout.bladeTupList):
            bitmap = 0
            for b in blade_tuple:
                bitmap |= (1 << (b - 1))  # basis vectors are 1-indexed
            self._bitmap_to_idx[bitmap] = idx

    def _build_bivector_basis(self):
        """Build the 45 bivector generators of so(5,5)."""
        self.bivectors = []
        self.bivector_labels = []
        for i in range(10):
            for j in range(i+1, 10):
                self.bivectors.append(self.e[i] ^ self.e[j])
                self.bivector_labels.append(f'e{i+1}^e{j+1}')
        assert len(self.bivectors) == 45

    def _build_d4_roots(self):
        """
        Build the 24 D4 root system.
        D4 roots: +-e_i +- e_j for 1 <= i < j <= 4
        """
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
        """Lie bracket [A, B] = AB - BA."""
        return A * B - B * A

    def rotor(self, B, theta):
        """Construct rotor R = exp(-B*theta/2) for unit bivector B with B^2 = -1."""
        return np.cos(theta/2) - B * np.sin(theta/2)

    def pseudoscalar(self):
        """Construct the grade-10 pseudoscalar."""
        ps = self.e[0]
        for ei in self.e[1:]:
            ps = ps * ei
        return ps

    def mv_component(self, mv, bitmap):
        """Extract the coefficient of a specific blade by its bitmap."""
        idx = self._bitmap_to_idx.get(bitmap)
        if idx is None:
            return 0.0
        return float(mv.value[idx])

    def vector_component(self, mv, idx):
        """Extract coefficient of e_{idx+1} (0-indexed)."""
        bitmap = 1 << idx
        return self.mv_component(mv, bitmap)

    def bivector_component(self, mv, idx):
        """Extract coefficient of the idx-th bivector e_i^e_j."""
        i, j = self._bivector_idx_to_pair(idx)
        bitmap = (1 << i) | (1 << j)
        return self.mv_component(mv, bitmap)

    def _bivector_idx_to_pair(self, idx):
        """Convert flat bivector index to (i,j) pair, 0-indexed."""
        count = 0
        for i in range(10):
            for j in range(i+1, 10):
                if count == idx:
                    return i, j
                count += 1
        raise ValueError(f"Invalid bivector index {idx}")

    def bivector_to_matrix(self, B):
        """
        Convert a bivector to its 10x10 matrix in the fundamental representation.
        M_ab = coefficient of e_{a+1} in [B, e_{b+1}]
        """
        M = np.zeros((10, 10))
        for a in range(10):
            for b in range(10):
                comm = self.commutator(B, self.e[b])
                M[a, b] = self.vector_component(comm, a)
        return M

    def verify_so55_algebra(self):
        """Verify the so(5,5) Lie algebra structure."""
        print("=== Verifying so(5,5) Lie algebra ===")

        # Bivector squares
        print("\nBivector squares (scalar part):")
        for B, label in zip(self.bivectors[:6], self.bivector_labels[:6]):
            sq = B * B
            print(f"  {label}^2 = {float(sq(0)):.1f}")
        print("  ...")

        # Jacobi identity
        print("\nJacobi identity checks:")
        test_triples = [(0, 1, 2), (0, 5, 6), (10, 20, 30), (0, 12, 24)]
        for i, j, k in test_triples:
            Bi, Bj, Bk = self.bivectors[i], self.bivectors[j], self.bivectors[k]
            jacobi = (self.commutator(Bi, self.commutator(Bj, Bk)) +
                     self.commutator(Bj, self.commutator(Bk, Bi)) +
                     self.commutator(Bk, self.commutator(Bi, Bj)))
            max_val = max(abs(v) for v in jacobi.value)
            status = "OK" if max_val < 1e-10 else f"FAIL (max={max_val:.2e})"
            print(f"  [{self.bivector_labels[i]}, {self.bivector_labels[j]}, {self.bivector_labels[k]}]: {status}")

        print(f"\nBivector count: {len(self.bivectors)} (expected 45)")
        print(f"D4 root count: {len(self.d4_roots)} (expected 24)")

        # D4 root norms
        print("\nD4 root norms (first 4):")
        for r, label in zip(self.d4_roots[:4], self.d4_root_labels[:4]):
            r_sq = float((r * r)(0))
            print(f"  {label}^2 = {r_sq:.1f}")

    def generate_certificates(self) -> Dict:
        """
        Generate certificates for the Lean HestenesAffineO55ClosureBridge.
        """
        certs = {}

        # 1. Pseudoscalar
        ps = self.pseudoscalar()
        ps_sq = ps * ps
        certs['pseudoscalar_sq'] = float(ps_sq(0))

        # 2. so(5,5) matrix representations (first 10 generators)
        certs['so55_matrices'] = []
        for B, label in zip(self.bivectors[:10], self.bivector_labels[:10]):
            M = self.bivector_to_matrix(B)
            certs['so55_matrices'].append({
                'label': label,
                'matrix': M.tolist()
            })

        # 3. D4 root data
        certs['d4_root_labels'] = self.d4_root_labels
        certs['d4_roots_as_vectors'] = []
        for r in self.d4_roots:
            vec = [self.vector_component(r, i) for i in range(4)]
            certs['d4_roots_as_vectors'].append(vec)

        # 4. Structure constants (nonzero ones for first 10 generators)
        certs['structure_constants'] = {}
        for i in range(min(10, len(self.bivectors))):
            for j in range(i+1, min(10, len(self.bivectors))):
                comm = self.commutator(self.bivectors[i], self.bivectors[j])
                for k in range(len(self.bivectors)):
                    coeff = self.bivector_component(comm, k)
                    if abs(coeff) > 1e-10:
                        certs['structure_constants'][(i, j, k)] = coeff

        # 5. so(4) subalgebra generators (first 6 bivectors: e_i^e_j for i,j in 0..3)
        certs['so4_generator_indices'] = [
            self._bivector_pair_to_idx(i, j) for i in range(4) for j in range(i+1, 4)
        ]

        return certs

    def _bivector_pair_to_idx(self, i, j):
        """Convert (i,j) pair to flat bivector index. i < j, 0-indexed."""
        count = 0
        for ii in range(10):
            for jj in range(ii+1, 10):
                if ii == i and jj == j:
                    return count
                count += 1
        raise ValueError(f"Invalid pair ({i},{j})")


def main():
    print("=" * 60)
    print("Cl(5,5) and O(5,5) Implementation")
    print("=" * 60)

    cl = Clifford55()

    # Basic properties
    print(f"\nCl(5,5) dimension: {cl.layout.gaDims}")
    print(f"Signature: {cl.layout.sig}")
    ps = cl.pseudoscalar()
    print(f"Pseudoscalar^2: {float(ps*ps):.1f}")

    # Verify Lie algebra
    cl.verify_so55_algebra()

    # Generate certificates
    print("\n=== Generating certificates ===")
    certs = cl.generate_certificates()
    print(f"Pseudoscalar^2: {certs['pseudoscalar_sq']}")
    print(f"so(5,5) matrices (sample): {len(certs['so55_matrices'])}")
    print(f"D4 roots: {len(certs['d4_root_labels'])}")
    print(f"SO(4) generator indices: {certs['so4_generator_indices']}")
    print(f"Nonzero structure constants: {len(certs['structure_constants'])}")

    # Sample structure constants
    print("\nSample structure constants f_{ijk}:")
    for (i, j, k), val in list(certs['structure_constants'].items())[:10]:
        print(f"  f_{{{cl.bivector_labels[i]}, {cl.bivector_labels[j]}, {cl.bivector_labels[k]}}} = {val:.4f}")

    # Verify a matrix representation
    print("\n=== Sample matrix: e1^e2 ===")
    M = cl.bivector_to_matrix(cl.bivectors[0])
    print(f"Shape: {M.shape}")
    print(f"Nonzero entries:")
    for a in range(10):
        for b in range(10):
            if abs(M[a, b]) > 1e-10:
                print(f"  M[{a},{b}] = {M[a,b]:.1f}")

    # Check antisymmetry: M should be antisymmetric in the appropriate metric
    print(f"\nM + M^T max: {np.max(M + M.T):.2e}")

    print("\nDone.")


if __name__ == '__main__':
    main()
