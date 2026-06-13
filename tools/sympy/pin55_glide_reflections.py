#!/usr/bin/env python3
"""Exact 32x32 real spinor verifier for finite Pin(5,5) reflection cores.

This is the assertion-first companion to
  lean/InfoGeometry/OperatorAlgebra/Pin55GlideStructure.lean

It constructs a real irreducible 32x32 representation of Cl(5,5) using a
Jordan-Wigner tensor pattern:
  gamma_pos[r] = C^⊗r ⊗ A ⊗ I...
  gamma_neg[r] = C^⊗r ⊗ B ⊗ I...
where A^2 = C^2 = +I, B^2 = -I, and A,B,C mutually anticommute as needed.

Important sign audit: for signature (5,5), the pseudoscalar/volume element
K = γ_1 ... γ_10 squares to +I in this convention, not -I.  The script asserts
that value and refuses the false -I claim.
"""
from __future__ import annotations

import sympy as sp

I2 = sp.eye(2)
A = sp.Matrix([[0, 1], [1, 0]])      # square +I
B = sp.Matrix([[0, 1], [-1, 0]])     # square -I
C = sp.Matrix([[1, 0], [0, -1]])     # square +I, anticommutes with A and B
I32 = sp.eye(32)
Z32 = sp.zeros(32)


def kron_all(parts: list[sp.Matrix]) -> sp.Matrix:
    out = parts[0]
    for part in parts[1:]:
        out = sp.kronecker_product(out, part)
    return sp.Matrix(out)


def gamma_pair(r: int) -> tuple[sp.Matrix, sp.Matrix]:
    prefix = [C] * r
    suffix = [I2] * (4 - r)
    return kron_all(prefix + [A] + suffix), kron_all(prefix + [B] + suffix)


def build_gammas() -> list[sp.Matrix]:
    pos, neg = [], []
    for r in range(5):
        gp, gn = gamma_pair(r)
        pos.append(gp)
        neg.append(gn)
    return pos + neg


def verify_clifford(gammas: list[sp.Matrix]) -> None:
    signs = [1] * 5 + [-1] * 5
    for i, gamma in enumerate(gammas):
        assert gamma.shape == (32, 32)
        assert gamma * gamma == signs[i] * I32
    for i in range(10):
        for j in range(10):
            anti = gammas[i] * gammas[j] + gammas[j] * gammas[i]
            expected = 2 * signs[i] * I32 if i == j else Z32
            assert anti == expected


def verify_volume(gammas: list[sp.Matrix]) -> None:
    K = gammas[0]
    for gamma in gammas[1:]:
        K = K * gamma
    assert K * K == I32
    assert K * K != -I32
    for gamma in gammas:
        # Even dimension volume element anticommutes with every odd generator.
        assert K * gamma + gamma * K == Z32


def verify_two_generator_glide_core(gammas: list[sp.Matrix]) -> None:
    gamma_space = gammas[0]
    gamma_time = gammas[5]
    glide_core = gamma_space * gamma_time
    assert gamma_space * gamma_space == I32
    assert gamma_time * gamma_time == -I32
    assert gamma_space * gamma_time + gamma_time * gamma_space == Z32
    assert gamma_space * glide_core == gamma_time
    assert glide_core * gamma_space == -gamma_time
    assert glide_core * glide_core == I32


def main() -> None:
    gammas = build_gammas()
    verify_clifford(gammas)
    verify_volume(gammas)
    verify_two_generator_glide_core(gammas)
    print("OK pin55_glide_reflections: exact 32x32 real Cl(5,5) gamma system verified")
    print("OK signatures: five +I squares, five -I squares, full anticommutation")
    print("OK glide core: gamma_space*(gamma_space*gamma_time)=gamma_time and square +I")
    print("SIGN AUDIT: Cl(5,5) volume element K^2 = +I32; the proposed K^2=-I32 is false")


if __name__ == "__main__":
    main()
