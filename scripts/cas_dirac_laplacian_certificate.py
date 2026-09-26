#!/usr/bin/env python3
"""
cas_dirac_laplacian_certificate.py

Symbolic CAS Certificate Generator for Graph Dirac Laplacians.
Computes and verifies exact rational matrices for:
- canonicalChainComplex (path graph P3: 0 -> 1 -> 2)
- canonicalTriangleComplex (triangle graph K3: 0 -> 1, 0 -> 2, 1 -> 2)
- canonicalDigonComplex (digon graph: 0 -> 1, 1 -> 0)

Verifies:
1. Boundary operators ∂₁ and ∂₁ᵀ
2. Graph Dirac operator D = [0, ∂₁ᵀ; ∂₁, 0]
3. Dirac square D²
4. 0-Laplacian Δ₀ = ∂₁ᵀ ∂₁
5. Down 1-Laplacian Δ₁_down = ∂₁ ∂₁ᵀ
6. Exact block-diagonal decomposition: D² = Δ₀ ⊕ Δ₁_down
7. Trace identity: Tr(D²) = Tr(Δ₀) + Tr(Δ₁_down)
"""

from __future__ import annotations
import json
import sys
from typing import Any, Dict, List, Tuple
import sympy as sp


def build_complex_matrices(name: str, n_vertices: int, edges: List[Tuple[int, int]]) -> Dict[str, Any]:
    """
    Given vertex count and directed edges, computes all Hodge-Dirac operators symbolically.
    """
    n0 = n_vertices
    n1 = len(edges)
    dim = n0 + n1

    # 1. Boundary matrix ∂₁: (n1 × n0)
    # Row e = (u, v): -1 at u, +1 at v, 0 elsewhere
    b1_entries = [[sp.Rational(0) for _ in range(n0)] for _ in range(n1)]
    for i, (u, v) in enumerate(edges):
        b1_entries[i][u] = sp.Rational(-1)
        b1_entries[i][v] = sp.Rational(1)

    b1 = sp.Matrix(b1_entries)
    b1_t = b1.transpose()

    # 2. Diagonal block Laplacians
    delta0 = b1_t * b1        # n0 × n0
    delta1_down = b1 * b1_t   # n1 × n1

    # 3. Full Dirac operator D: dim × dim
    # D = [   0      ∂₁ᵀ ]
    #     [  ∂₁       0  ]
    zero_00 = sp.zeros(n0, n0)
    zero_11 = sp.zeros(n1, n1)
    dirac = sp.BlockMatrix([[zero_00, b1_t], [b1, zero_11]]).as_explicit()

    # 4. Dirac Square D²
    dirac_sq = dirac * dirac

    # 5. Expected block-diagonal matrix Δ₀ ⊕ Δ₁_down
    zero_01 = sp.zeros(n0, n1)
    zero_10 = sp.zeros(n1, n0)
    expected_block = sp.BlockMatrix([[delta0, zero_01], [zero_10, delta1_down]]).as_explicit()

    # 6. Verification checks
    diff_block = dirac_sq - expected_block
    is_block_diag = (diff_block == sp.zeros(dim, dim))

    tr_dirac_sq = dirac_sq.trace()
    tr_delta0 = delta0.trace()
    tr_delta1_down = delta1_down.trace()
    tr_sum = tr_delta0 + tr_delta1_down
    is_trace_equal = (tr_dirac_sq == tr_sum)

    # Upper-right and lower-left blocks are identically zero
    upper_right_zero = all(dirac_sq[i, n0 + j] == 0 for i in range(n0) for j in range(n1))
    lower_left_zero = all(dirac_sq[n0 + j, i] == 0 for i in range(n0) for j in range(n1))

    # Upper-left agrees with delta0, lower-right agrees with delta1_down
    upper_left_agrees = all(dirac_sq[i, j] == delta0[i, j] for i in range(n0) for j in range(n0))
    lower_right_agrees = all(dirac_sq[n0 + i, n0 + j] == delta1_down[i, j] for i in range(n1) for j in range(n1))

    assert is_block_diag, f"Block decomposition failed for {name}"
    assert is_trace_equal, f"Trace equality failed for {name}"
    assert upper_right_zero and lower_left_zero, f"Off-diagonal zero failed for {name}"
    assert upper_left_agrees and lower_right_agrees, f"Block agreement failed for {name}"

    def mat_to_list(m: sp.Matrix) -> List[List[int]]:
        return [[int(m[i, j]) for j in range(m.cols)] for i in range(m.rows)]

    def mat_to_lean(m: sp.Matrix) -> str:
        rows = []
        for i in range(m.rows):
            elems = []
            for j in range(m.cols):
                val = int(m[i, j])
                if i == 0 and j == 0:
                    elems.append(f"({val} : Rat)")
                else:
                    elems.append(str(val))
            rows.append("#[" + ", ".join(elems) + "]")
        return "#[\n        " + ",\n        ".join(rows) + "]"

    return {
        "name": name,
        "nodes": n0,
        "edges_count": n1,
        "dim": dim,
        "edges": edges,
        "boundary1": mat_to_list(b1),
        "laplacian0": mat_to_list(delta0),
        "laplacian1_down": mat_to_list(delta1_down),
        "dirac": mat_to_list(dirac),
        "dirac_sq": mat_to_list(dirac_sq),
        "dirac_sq_lean": mat_to_lean(dirac_sq),
        "trace_dirac_sq": int(tr_dirac_sq),
        "trace_delta0": int(tr_delta0),
        "trace_delta1_down": int(tr_delta1_down),
        "verified": True
    }


def generate_all_certificates() -> Dict[str, Any]:
    # 1. Chain complex: 3 vertices, edges (0, 1), (1, 2)
    chain = build_complex_matrices(
        "canonicalChainComplex",
        n_vertices=3,
        edges=[(0, 1), (1, 2)]
    )

    # 2. Triangle complex: 3 vertices, edges (0, 1), (0, 2), (1, 2)
    triangle = build_complex_matrices(
        "canonicalTriangleComplex",
        n_vertices=3,
        edges=[(0, 1), (0, 2), (1, 2)]
    )

    # 3. Digon complex: 2 vertices, edges (0, 1), (1, 0)
    digon = build_complex_matrices(
        "canonicalDigonComplex",
        n_vertices=2,
        edges=[(0, 1), (1, 0)]
    )

    return {
        "canonicalChainComplex": chain,
        "canonicalTriangleComplex": triangle,
        "canonicalDigonComplex": digon
    }


def main():
    print("=" * 60)
    print("CAS Dirac Laplacian Exact Rational Certificate Generator")
    print("=" * 60)

    certs = generate_all_certificates()

    for key, cert in certs.items():
        print(f"\n[Complex: {key}]")
        print(f"  Nodes: {cert['nodes']}, Edges: {cert['edges_count']}, Total Dirac Dim: {cert['dim']}")
        print(f"  Tr(Δ₀) = {cert['trace_delta0']}, Tr(down-Δ₁) = {cert['trace_delta1_down']}, Tr(D²) = {cert['trace_dirac_sq']}")
        print(f"  Block decomposition D² = Δ₀ ⊕ down-Δ₁ : VERIFIED")
        print(f"  Trace equality Tr(D²) = Tr(Δ₀) + Tr(down-Δ₁) : VERIFIED")
        print("  D² matrix:")
        for row in cert["dirac_sq"]:
            print(f"    {row}")

    print("\n" + "=" * 60)
    print("All CAS Dirac Laplacian certificates mathematically verified.")
    print("=" * 60)


if __name__ == "__main__":
    main()
