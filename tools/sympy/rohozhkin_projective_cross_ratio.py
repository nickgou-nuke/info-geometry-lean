import sympy as sp

zi, zj, zk, zl, zm = sp.symbols("z_i z_j z_k z_l z_m", nonzero=True)


def affine_chart(zi, zk, x):
    return sp.simplify((x - zk) / (zi - zk))


def flip_block(zi, zk, zj, zl):
    denom = zi - zk
    return sp.Matrix([
        [(zi - zl) / denom, (zi - zj) / denom],
        [(zl - zk) / denom, (zj - zk) / denom],
    ])


def cross_ratio(a, b, c, d):
    return sp.simplify(((a - b) * (c - d)) / ((a - c) * (b - d)))


def appendix_pentagon_matrices():
    gamma1 = sp.Matrix([
        [1, 0, 0],
        [0, (zi - zm) / (zi - zl), (zi - zk) / (zi - zl)],
        [0, (zm - zl) / (zi - zl), (zk - zl) / (zi - zl)],
    ])
    gamma2 = sp.Matrix([
        [(zi - zm) / (zi - zk), (zi - zj) / (zi - zk), 0],
        [(zm - zk) / (zi - zk), (zj - zk) / (zi - zk), 0],
        [0, 0, 1],
    ])
    gamma3 = sp.Matrix([
        [1, 0, 0],
        [0, (zk - zl) / (zk - zm), (zk - zj) / (zk - zm)],
        [0, (zl - zm) / (zk - zm), (zj - zm) / (zk - zm)],
    ])
    gamma4 = sp.Matrix([
        [(zj - zl) / (zj - zm), 0, (zj - zi) / (zj - zm)],
        [(zl - zm) / (zj - zm), 0, (zi - zm) / (zj - zm)],
        [0, 1, 0],
    ])
    gamma5 = sp.Matrix([
        [(zj - zk) / (zj - zl), 0, (zj - zi) / (zj - zl)],
        [(zk - zl) / (zj - zl), 0, (zi - zl) / (zj - zl)],
        [0, 1, 0],
    ])
    return gamma1, gamma2, gamma3, gamma4, gamma5


def verify_affine_chart_block():
    A = flip_block(zi, zk, zj, zl)
    tj = affine_chart(zi, zk, zj)
    tl = affine_chart(zi, zk, zl)
    expected = sp.Matrix([
        [1 - tl, 1 - tj],
        [tl, tj],
    ])
    assert sp.simplify(A - expected) == sp.zeros(2)
    print("AFFINE_CHART_BLOCK: OK")


def verify_column_sums():
    A = flip_block(zi, zk, zj, zl)
    assert sp.simplify(A[0, 0] + A[1, 0] - 1) == 0
    assert sp.simplify(A[0, 1] + A[1, 1] - 1) == 0
    print("COLUMN_SUMS: OK")


def verify_determinant_formula():
    A = flip_block(zi, zk, zj, zl)
    assert sp.simplify(A.det() - (zj - zl) / (zi - zk)) == 0
    print("DETERMINANT_FORMULA: OK")


def verify_cross_ratio_extraction():
    A = flip_block(zi, zk, zj, zl)
    extracted = sp.simplify((A[0, 1] * A[1, 0]) / (A[0, 0] * A[1, 1]))
    target = cross_ratio(zi, zj, zl, zk)
    assert sp.simplify(extracted - target) == 0
    print("CROSS_RATIO_EXTRACTION: OK")


def verify_reverse_flip_inverse():
    A = flip_block(zi, zk, zj, zl)
    B = flip_block(zj, zl, zi, zk)
    assert sp.simplify(A * B - sp.eye(2)) == sp.zeros(2)
    assert sp.simplify(B * A - sp.eye(2)) == sp.zeros(2)
    print("REVERSE_FLIP_INVERSE: OK")


def verify_pentagon_chart_cocycle():
    gamma1, gamma2, gamma3, gamma4, gamma5 = appendix_pentagon_matrices()
    prod = sp.simplify(gamma5 * gamma4 * gamma3 * gamma2 * gamma1)
    assert sp.simplify(prod - sp.eye(3)) == sp.zeros(3)
    print("PENTAGON_CHART_COCYCLE: OK")


def verify_rational_sample():
    vals = {zi: sp.Rational(1), zj: sp.Rational(2), zk: sp.Rational(3), zl: sp.Rational(5)}
    A = flip_block(vals[zi], vals[zk], vals[zj], vals[zl])
    extracted = sp.simplify((A[0, 1] * A[1, 0]) / (A[0, 0] * A[1, 1]))
    target = cross_ratio(vals[zi], vals[zj], vals[zl], vals[zk])
    assert extracted == target
    print("RATIONAL_SAMPLE: OK")
    print(A)
    print(f"cross_ratio = {target}")


if __name__ == "__main__":
    verify_affine_chart_block()
    verify_column_sums()
    verify_determinant_formula()
    verify_cross_ratio_extraction()
    verify_reverse_flip_inverse()
    verify_pentagon_chart_cocycle()
    verify_rational_sample()
    print("ROHOZHKIN_PROJECTIVE_BRIDGE_STATUS: CLOSED")
