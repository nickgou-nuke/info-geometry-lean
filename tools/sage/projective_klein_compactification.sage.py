#!/usr/bin/env sage
"""Exact-rational Sage audit for the projective Klein formula packet."""

from pathlib import Path
import subprocess

from sage.all import Matrix, QQ, identity_matrix, vector


def projectively_equal(a, b) -> bool:
    return a == b or a == -b


def main() -> None:
    i2 = identity_matrix(QQ, 2)
    minus_i2 = -i2
    twist_a = Matrix(QQ, [[1, 0], [0, -1]])
    parabolic_b = Matrix(QQ, [[1, 1], [0, 1]])
    parabolic_b_inv = Matrix(QQ, [[1, -1], [0, 1]])
    mobius_s = Matrix(QQ, [[0, -1], [1, 0]])

    assert projectively_equal(i2, minus_i2)
    assert minus_i2 * minus_i2 == i2
    assert twist_a * twist_a == i2
    assert parabolic_b * parabolic_b_inv == i2
    assert parabolic_b_inv * parabolic_b == i2
    assert twist_a * parabolic_b * twist_a == parabolic_b_inv
    assert twist_a * parabolic_b * twist_a * parabolic_b == i2
    assert mobius_s * vector(QQ, [3, 1]) == vector(QQ, [-1, 3])
    assert projectively_equal(mobius_s * mobius_s, i2)

    gap_file = Path(__file__).resolve().parents[1] / "gap" / "projective_klein_compactification.g"
    gap_run = subprocess.run(
        ["gap", "-q", str(gap_file)],
        check=True,
        capture_output=True,
        text=True,
    )
    assert gap_run.returncode == 0

    print("projective Klein compactification Sage/GAP audit: ok")


main()
