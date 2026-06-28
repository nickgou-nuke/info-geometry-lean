from sage.all import CDF, I, Matrix, infinity


def contragredient(M):
    return Matrix(CDF, [[M[1, 1], -M[0, 1]], [-M[1, 0], M[0, 0]]])


def fixed_points(M):
    a, b, c, d = M[0, 0], M[0, 1], M[1, 0], M[1, 1]
    if c == 0:
        return [infinity, 0] if b == 0 else [infinity, b / (d - a)]
    disc = (d - a) ** 2 + 4 * b * c
    sdisc = disc.sqrt()
    return [((a - d) + sdisc) / (2 * c), ((a - d) - sdisc) / (2 * c)]


def report(M):
    pts = fixed_points(M)
    vals = M.eigenvalues()
    eta = Matrix(CDF, [[3, 5]])
    theta = Matrix(CDF, [[7], [11]])
    lhs = (eta * contragredient(M).transpose() * M * theta)[0, 0]
    rhs = (eta * theta)[0, 0]
    assert abs(lhs - rhs) < 1e-9
    print('matrix =', M)
    print('eigenvalues =', vals)
    print('fixed_points =', pts)
    print('pairing_invariant =', abs(lhs - rhs) < 1e-9)


if __name__ == '__main__':
    M = Matrix(CDF, [[2, 0], [0, 0.5]])
    assert abs(M.det() - 1) < 1e-9
    report(M)
    q = Matrix(CDF, [[1 + I, 1 + I], [-1 + I, 1 - I]])
    print('hurwitz_matrix_det =', q.det())
    print('MOBIUS_SAGE_OK')
