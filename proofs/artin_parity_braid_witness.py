#!/usr/bin/env python3
"""Artin parity braid witness.

This script fixes the common phase/sign pitfall:

- `twoAtomParity = sigma3 * iSigma2 = sigma_x`, so `G^2 = I` and `G^3 = G`.
- The relation `G^3 = -G` belongs to `iSigma2`, because `(iSigma2)^2 = -I`.
- A genuine two-body 4x4 R-matrix witness is checked on four strands
  (16x16 matrices): `R_12 R_23 R_12 = R_23 R_12 R_23` and
  `R_12 R_34 = R_34 R_12`.
- A nondegenerate adjacent Artin/Yang--Baxter witness is also supplied by three
  anticommuting Majorana/Clifford modes and exchange gates
  `U_i = (I + gamma_i gamma_{i+1}) / sqrt(2)` on C^2 ⊗ C^2 ⊗ C^2.
"""

import sympy as sp


def assert_zero(name: str, matrix: sp.Matrix) -> None:
    residue = matrix.applyfunc(lambda x: sp.simplify(sp.expand_func(x).rewrite(sp.exp)))
    ok = residue == sp.zeros(*residue.shape)
    print(f"{name}: {'PASS' if ok else 'FAIL'}")
    if not ok:
        print(residue)
        raise SystemExit(1)


def kron(*matrices: sp.Matrix) -> sp.Matrix:
    out = matrices[0]
    for matrix in matrices[1:]:
        out = sp.kronecker_product(out, matrix)
    return out


def main() -> int:
    print("=== OMEGA AUTOMATH: ARTIN BRAID GATE VERIFIER ===")

    sigma0 = sp.eye(2)
    sigma1 = sp.Matrix([[0, 1], [1, 0]])
    sigma2 = sp.Matrix([[0, -sp.I], [sp.I, 0]])
    sigma3 = sp.Matrix([[1, 0], [0, -1]])
    i_sigma2 = sp.I * sigma2

    gate = sigma3 * i_sigma2
    print("\n[twoAtomParity = sigma3 * iSigma2]")
    sp.pprint(gate)

    assert_zero("twoAtomParity equals sigma_x", gate - sigma1)
    assert_zero("twoAtomParity^2 = I", gate**2 - sigma0)
    assert_zero("twoAtomParity^3 = twoAtomParity", gate**3 - gate)
    assert_zero("iSigma2^3 = -iSigma2", i_sigma2**3 + i_sigma2)

    # Degenerate/uniform Lean representation: every generator maps to the same parity channel.
    P2 = kron(sigma3, sigma3)
    g0 = P2
    g1 = P2
    assert_zero("degenerate adjacent Artin: g0*g1*g0 = g1*g0*g1", g0 * g1 * g0 - g1 * g0 * g1)
    assert_zero("degenerate separated Artin: g0*g1 = g1*g0", g0 * g1 - g1 * g0)

    print("\n[Two-body 4x4 R-matrix witness on four strands / 16x16 space]")
    R = sp.Matrix(
        [
            [1, 0, 0, 0],
            [0, 0, sp.I, 0],
            [0, sp.I, 0, 0],
            [0, 0, 0, 1],
        ]
    )
    R12 = kron(R, sigma0, sigma0)
    R23 = kron(sigma0, R, sigma0)
    R34 = kron(sigma0, sigma0, R)
    assert_zero("two-body adjacent Artin: R12*R23*R12 = R23*R12*R23", R12 * R23 * R12 - R23 * R12 * R23)
    assert_zero("two-body separated Artin: R12*R34 = R34*R12", R12 * R34 - R34 * R12)

    print("\n[Nondegenerate three-atom Majorana/Clifford witness on C^2 ⊗ C^2 ⊗ C^2]")
    gamma1 = kron(sigma1, sigma0, sigma0)
    gamma2 = kron(sigma2, sigma0, sigma0)
    gamma3 = kron(sigma3, sigma1, sigma0)

    for idx, gamma in enumerate([gamma1, gamma2, gamma3], start=1):
        assert_zero(f"gamma{idx}^2 = I", gamma * gamma - sp.eye(8))

    assert_zero("{gamma1,gamma2}=0", gamma1 * gamma2 + gamma2 * gamma1)
    assert_zero("{gamma2,gamma3}=0", gamma2 * gamma3 + gamma3 * gamma2)
    assert_zero("{gamma1,gamma3}=0", gamma1 * gamma3 + gamma3 * gamma1)

    U1 = (sp.eye(8) + gamma1 * gamma2) / sp.sqrt(2)
    U2 = (sp.eye(8) + gamma2 * gamma3) / sp.sqrt(2)
    assert_zero("nondegenerate adjacent Artin/Yang--Baxter: U1*U2*U1 = U2*U1*U2", U1 * U2 * U1 - U2 * U1 * U2)

    sep1 = kron(sigma1, sigma0, sigma0)
    sep3 = kron(sigma0, sigma0, sigma1)
    assert_zero("separated three-atom commutation", sep1 * sep3 - sep3 * sep1)

    print("\n=== SUCCESS: ARTIN BRAID TOPOLOGIES VERIFIED ===")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
