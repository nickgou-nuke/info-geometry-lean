#!/usr/bin/env python3
"""Witness for the corrected Cl(4,C) -> M4(C) matrix representation.

The representation uses the graded tensor construction

    e1 = (i sigma1) tensor sigma3
    e2 = (i sigma2) tensor sigma3
    e3 = I2 tensor (i sigma1)
    e4 = I2 tensor (i sigma2)

so all generators square to -I4 and pairwise anticommute.  The script also
checks that the ungraded formula from the prose corridor fails the mixed
anticommutator test, which is why the sigma3 tail is required.
"""

import sympy as sp


I = sp.I
sigma1 = sp.Matrix([[0, 1], [1, 0]])
sigma2 = sp.Matrix([[0, -I], [I, 0]])
sigma3 = sp.Matrix([[1, 0], [0, -1]])
I2 = sp.eye(2)
I4 = sp.eye(4)


def kron(a: sp.Matrix, b: sp.Matrix) -> sp.Matrix:
    return sp.kronecker_product(a, b)


def flatten(m: sp.Matrix) -> list[sp.Expr]:
    return [sp.simplify(m[r, c]) for r in range(m.rows) for c in range(m.cols)]


def word(gens: list[sp.Matrix], mask: int) -> sp.Matrix:
    out = I4
    for i, g in enumerate(gens):
        if mask & (1 << i):
            out = out * g
    return sp.simplify(out)


def assert_zero(m: sp.Matrix, label: str) -> None:
    if any(sp.simplify(x) != 0 for x in m):
        raise AssertionError(f"{label} is not zero:\n{m}")


def assert_nonzero(m: sp.Matrix, label: str) -> None:
    if all(sp.simplify(x) == 0 for x in m):
        raise AssertionError(f"{label} unexpectedly vanished")


def main() -> None:
    a1 = I * sigma1
    a2 = I * sigma2

    gens = [
        kron(a1, sigma3),
        kron(a2, sigma3),
        kron(I2, a1),
        kron(I2, a2),
    ]

    for i, g in enumerate(gens, start=1):
        assert_zero(g * g + I4, f"e{i}^2 + I")

    for i in range(len(gens)):
        for j in range(i + 1, len(gens)):
            assert_zero(gens[i] * gens[j] + gens[j] * gens[i], f"e{i + 1}e{j + 1}+e{j + 1}e{i + 1}")

    basis = [word(gens, mask) for mask in range(16)]
    flat = sp.Matrix([flatten(m) for m in basis])
    det = sp.simplify(flat.det())
    if det == 0:
        raise AssertionError("the 16 Clifford words do not span M4(C)")

    # The ungraded construction from the prose corridor is not a Clifford
    # representation: the first old generator and first new generator commute
    # rather than anticommute.
    bad_e1 = kron(I2, a1)
    bad_e3 = kron(sigma3, a1)
    assert_nonzero(bad_e1 * bad_e3 + bad_e3 * bad_e1, "ungraded mixed anticommutator")

    print("Cl(4,C) graded tensor generators verified")
    print("16 Clifford words form a basis of M4(C)")
    print(f"basis determinant = {det}")
    print("ungraded prompt formula rejected by mixed anticommutator test")


if __name__ == "__main__":
    main()
