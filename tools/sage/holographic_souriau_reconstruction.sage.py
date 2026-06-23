#!/usr/bin/env sage -python
"""
Sage exact-rational certificate for the finite holographic Souriau reconstruction
lane.

Checks:
- O(5,5) split metric is involutive and symmetric
- Brillouin twist squares to -I
- Brillouin glide squares to I
- glide/twist anticommute
- scalar modular laser commutes with all displayed su(3) Chevalley generators
"""

from sage.all import Matrix, QQ, diagonal_matrix, identity_matrix, zero_matrix


def assert_zero(m, label: str) -> None:
    if m != zero_matrix(QQ, m.nrows(), m.ncols()):
        raise AssertionError(f"{label} failed:\n{m}")


def main() -> None:
    print("=== Holographic Souriau Reconstruction Sage certificate ===")

    o55 = diagonal_matrix(QQ, [1, 1, 1, 1, 1, -1, -1, -1, -1, -1])
    assert o55 * o55 == identity_matrix(QQ, 10)
    assert o55.transpose() == o55
    print("PASS: O(5,5) split metric is involutive and symmetric")

    T = Matrix(QQ, [[0, -1], [1, 0]])
    K = Matrix(QQ, [[1, 0], [0, -1]])
    assert T * T == -identity_matrix(QQ, 2)
    assert K * K == identity_matrix(QQ, 2)
    assert K * T == -(T * K)
    print("PASS: Brillouin twist/glide relations")

    C = 2 * identity_matrix(QQ, 3)
    gens = [
        Matrix(QQ, [[0,1,0],[0,0,0],[0,0,0]]),
        Matrix(QQ, [[0,0,0],[1,0,0],[0,0,0]]),
        Matrix(QQ, [[0,0,0],[0,0,1],[0,0,0]]),
        Matrix(QQ, [[0,0,0],[0,0,0],[0,1,0]]),
        Matrix(QQ, [[0,0,1],[0,0,0],[0,0,0]]),
        Matrix(QQ, [[0,0,0],[0,0,0],[1,0,0]]),
        Matrix(QQ, [[1,0,0],[0,-1,0],[0,0,0]]),
        Matrix(QQ, [[0,0,0],[0,1,0],[0,0,-1]]),
    ]
    for i, g in enumerate(gens):
        assert_zero(C * g - g * C, f"SU3 generator {i} commutator")
    print("PASS: scalar modular laser commutes with displayed su(3) generators")

    print("HOLOGRAPHIC_SOURIAU_RECONSTRUCTION_SAGE_OK")


if __name__ == '__main__':
    main()
