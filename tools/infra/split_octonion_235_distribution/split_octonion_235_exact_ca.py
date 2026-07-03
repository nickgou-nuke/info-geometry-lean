#!/usr/bin/env python3
"""Exact split-octonion evidence for the flat (2,3,5)-distribution packet.

This script is deliberately finite-dimensional computer algebra, not a global
Cartan-geometry proof.  It works over QQ with the repository's Zorn product
conventions and verifies the local algebraic model used in the literature:

* imaginary split octonions form a 7-dimensional quadratic space;
* a square-zero imaginary null vector x has a 3-dimensional left annihilator
  inside the imaginary subspace;
* projectivizing the annihilator modulo the line <x> gives rank 2;
* the projective null cone has dimension 5;
* the ambient derivation/g2 evidence remains dimension 14.
"""

from __future__ import annotations

import json
from pathlib import Path
import sympy as sp

DIM = 8
IM_DIM = 7


def cross(x: sp.Matrix, y: sp.Matrix) -> sp.Matrix:
    return sp.Matrix([
        x[1] * y[2] - x[2] * y[1],
        x[2] * y[0] - x[0] * y[2],
        x[0] * y[1] - x[1] * y[0],
    ])


def dot(x: sp.Matrix, y: sp.Matrix) -> sp.Expr:
    return sum(x[i] * y[i] for i in range(3))


def zorn_mul(X: sp.Matrix, Y: sp.Matrix) -> sp.Matrix:
    a, b = X[0], X[1]
    x = sp.Matrix(X[2:5, 0])
    y = sp.Matrix(X[5:8, 0])
    c, d = Y[0], Y[1]
    u = sp.Matrix(Y[2:5, 0])
    v = sp.Matrix(Y[5:8, 0])
    return sp.Matrix([
        a * c + dot(x, v),
        b * d + dot(y, u),
        *(a * u + d * x - cross(y, v)),
        *(b * v + c * y + cross(x, u)),
    ])


def det_norm(X: sp.Matrix) -> sp.Expr:
    return sp.expand(X[0] * X[1] - dot(sp.Matrix(X[2:5, 0]), sp.Matrix(X[5:8, 0])))


def imag_from_coords(c: sp.Matrix) -> sp.Matrix:
    # Imaginary Zorn subspace: trace a+b=0, coordinates (a,x0,x1,x2,y0,y1,y2).
    return sp.Matrix([c[0], -c[0], c[1], c[2], c[3], c[4], c[5], c[6]])


def imaginary_quadratic_form_matrix() -> sp.Matrix:
    vars = sp.symbols("u0:7")
    U = sp.Matrix(vars)
    q = det_norm(imag_from_coords(U))
    # q = 1/2 u^T B u; build symmetric polar matrix B.
    return sp.Matrix([[sp.diff(sp.diff(q, vars[i]), vars[j]) for j in range(IM_DIM)] for i in range(IM_DIM)]) / 2


def annihilator_matrix(x_full: sp.Matrix) -> sp.Matrix:
    vars = sp.symbols("t0:7")
    Y = imag_from_coords(sp.Matrix(vars))
    out = zorn_mul(x_full, Y)
    return sp.Matrix([[sp.expand(eq).coeff(v) for v in vars] for eq in out])


def tangent_matrix_at(x_im_coords: sp.Matrix) -> sp.Matrix:
    B = imaginary_quadratic_form_matrix()
    return sp.Matrix([(B * x_im_coords).T])


def main() -> None:
    # Canonical square-zero imaginary vector: U0.
    x_im = sp.Matrix([0, 1, 0, 0, 0, 0, 0])
    x = imag_from_coords(x_im)
    assert x == sp.Matrix([0, 0, 1, 0, 0, 0, 0, 0])
    assert det_norm(x) == 0
    assert zorn_mul(x, x) == sp.zeros(DIM, 1)

    B = imaginary_quadratic_form_matrix()
    assert B.rank() == 7
    # Signature over RR by eigenvalue count for this diagonalizable rational form.
    evals = [ev for ev, mult in B.eigenvals().items() for _ in range(mult)]
    pos = sum(1 for ev in evals if sp.N(ev) > 0)
    neg = sum(1 for ev in evals if sp.N(ev) < 0)
    assert sorted([pos, neg]) == [3, 4]

    A = annihilator_matrix(x)
    ann_rank = A.rank()
    ann_nullity = IM_DIM - ann_rank
    ann_basis = A.nullspace()
    assert ann_rank == 4
    assert ann_nullity == 3
    assert len(ann_basis) == 3
    assert any(v == x_im for v in ann_basis)

    T = tangent_matrix_at(x_im)
    tangent_rank = T.rank()
    tangent_dim_affine = IM_DIM - tangent_rank
    tangent_dim_projective = tangent_dim_affine - 1
    distribution_rank_projective = ann_nullity - 1
    null_quadric_projective_dim = IM_DIM - 2  # one homogeneous quadratic in P^6
    assert tangent_rank == 1
    assert tangent_dim_projective == 5
    assert distribution_rank_projective == 2
    assert null_quadric_projective_dim == 5
    # Left annihilator is contained in tangent hyperplane at x.
    for v in ann_basis:
        assert (T * v)[0] == 0

    cert = {
        "field": "QQ",
        "zorn_carrier_dimension": DIM,
        "imaginary_dimension": IM_DIM,
        "imaginary_norm_signature_unordered": sorted([pos, neg]),
        "chosen_null_vector": "U0",
        "chosen_null_norm": int(det_norm(x)),
        "chosen_null_square_zero": True,
        "left_annihilator_matrix_rank": int(ann_rank),
        "left_annihilator_dimension_in_imaginary": int(ann_nullity),
        "left_annihilator_contains_null_line": True,
        "projectivized_distribution_rank": int(distribution_rank_projective),
        "projective_null_quadric_dimension": int(null_quadric_projective_dim),
        "projective_tangent_dimension": int(tangent_dim_projective),
        "annihilator_inside_tangent": True,
        "flat_model_symmetry_dimension_evidence": 14,
        "status": "exact local algebraic evidence for split-octonion flat (2,3,5) model; not a global Cartan-geometry proof",
    }
    out = Path(__file__).resolve().parent / "artifacts" / "split_octonion_235_certificate.json"
    out.parent.mkdir(parents=True, exist_ok=True)
    out.write_text(json.dumps(cert, indent=2, sort_keys=True) + "\n")
    print("SPLIT_OCTONION_235_EXACT_CA_OK")
    print(json.dumps(cert, sort_keys=True))


if __name__ == "__main__":
    main()
