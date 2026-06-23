from sage.all import Matrix, PolynomialRing, QQ


def check(name, d0, n1, expected_b1):
    d1_rank = 0
    b1 = n1 - d1_rank - d0.rank()
    L1 = d0 * d0.transpose()
    harmonic_dim = n1 - L1.rank()
    if b1 != expected_b1:
        raise AssertionError((name, "b1", b1, expected_b1))
    if harmonic_dim != expected_b1:
        raise AssertionError((name, "harmonic", harmonic_dim, expected_b1))

    R = PolynomialRing(QQ, n1, "x")
    x = Matrix(R, n1, 1, R.gens())
    d0R = Matrix(R, d0)
    L1R = d0R * d0R.transpose()
    coclosed = d0R.transpose() * x
    residual = (x.transpose() * L1R * x)[0, 0] - (coclosed.transpose() * coclosed)[0, 0]
    if residual != 0:
        raise AssertionError((name, "energy", residual))

    print(f"{name}: rank(d0)={d0.rank()} b1={b1} dim ker L1={harmonic_dim} energy=ok")


path_d0 = Matrix(QQ, [[-1, 1, 0], [0, -1, 1]])
cycle_d0 = Matrix(QQ, [[-1, 1, 0], [0, -1, 1], [1, 0, -1]])

check("path-tree", path_d0, 2, 0)
check("triangle-cycle", cycle_d0, 3, 1)
