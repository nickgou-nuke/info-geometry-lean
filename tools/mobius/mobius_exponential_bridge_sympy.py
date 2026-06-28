#!/usr/bin/env python3
from __future__ import annotations

import sympy as sp


def sl2_matrix(A, B, C):
    return sp.Matrix([[A, B], [C, -A]])


def vector_field(A, B, C, z):
    return sp.expand(-C * z**2 + 2 * A * z + B)


def fixed_polynomial(M, z):
    a, b, c, d = M[0, 0], M[0, 1], M[1, 0], M[1, 1]
    return sp.expand(c * z**2 + (d - a) * z - b)


def verify_symbolic_cayley_hamilton():
    A, B, C = sp.symbols('A B C')
    M = sl2_matrix(A, B, C)
    detM = sp.expand(M.det())
    lhs = sp.expand(M * M)
    rhs = sp.expand((-detM) * sp.eye(2))
    assert sp.simplify(lhs - rhs) == sp.zeros(2)
    return detM


def verify_parabolic_flow():
    t, z = sp.symbols('t z')
    M = sl2_matrix(1, 1, -1)
    assert sp.expand(M * M) == sp.zeros(2)
    flow = sp.eye(2) + t * M
    assert sp.simplify(flow.det() - 1) == 0
    assert sp.simplify(flow.trace() - 2) == 0
    fp = sp.factor(fixed_polynomial(flow, z))
    roots = sp.solve(sp.Eq(fp, 0), z)
    return {
        'flow': flow,
        'determinant': sp.expand(flow.det()),
        'trace': sp.expand(flow.trace()),
        'fixed_polynomial': fp,
        'roots': roots,
    }


def verify_hyperbolic_elliptic_exponentials():
    t = sp.symbols('t', real=True)
    hyper = sl2_matrix(1, 0, -1)
    ell = sl2_matrix(0, 1, -1)
    hyper_exp = sp.simplify(sp.exp(t * hyper))
    ell_exp = sp.simplify(sp.exp(t * ell))
    assert sp.simplify(hyper_exp.det() - 1) == 0
    assert sp.simplify(ell_exp.det() - 1) == 0
    return {
        'hyperbolic_exp_00': sp.simplify(hyper_exp[0, 0]),
        'hyperbolic_exp_01': sp.simplify(hyper_exp[0, 1]),
        'elliptic_exp_00': sp.simplify(ell_exp[0, 0]),
        'elliptic_exp_01': sp.simplify(ell_exp[0, 1]),
    }


def main():
    detM = verify_symbolic_cayley_hamilton()
    para = verify_parabolic_flow()
    exp_reports = verify_hyperbolic_elliptic_exponentials()
    print('symbolic_trace_zero_square = (-det M) I with det(M) =', detM)
    print('[parabolic flow]')
    print('  flow =', para['flow'])
    print('  determinant =', para['determinant'])
    print('  trace =', para['trace'])
    print('  fixed_polynomial =', para['fixed_polynomial'])
    print('  roots =', para['roots'])
    print('[sample exponentials]')
    for k, v in exp_reports.items():
        print(f'  {k} = {v}')
    print('MOBIUS_EXPONENTIAL_BRIDGE_SYMPY_OK')


if __name__ == '__main__':
    main()
