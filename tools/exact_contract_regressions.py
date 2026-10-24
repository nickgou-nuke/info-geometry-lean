"""Exact finite witnesses for the three notes; not a Lean verification run.

Requires SymPy only for this audit program. The pruning runtime is standard-library only.
"""
from pathlib import Path
import itertools
import json
import sympy as sp


def dump_matrix(a):
    return [[str(a[i, j]) for j in range(a.cols)] for i in range(a.rows)]


def stein(a, b, x, k):
    return sum((a**i * x * b**i for i in range(k)), sp.zeros(a.rows, b.cols))


def main():
    checks = {}
    A = sp.Matrix([[1, 1], [0, 0]])
    D = A
    E = A * D
    C = A * E
    N = A * (sp.eye(2) - E)
    assert A*D == D*A and D*A*D == D and A**2*D == A
    assert E.T != E and N == sp.zeros(2)
    assert C*N.T == sp.zeros(2) and C.T*N == sp.zeros(2)
    checks['oblique_core_cross_products_vanish'] = {
        'passed': True, 'E': dump_matrix(E), 'N': dump_matrix(N),
        'projector_obliqueness_defect': dump_matrix(E*(sp.eye(2)-E.T))}

    A = sp.Matrix([[0, 1], [0, 0]])
    GL, GR = A*A.T, A.T*A
    assert GL*GR == GR*GL and GL != GR
    checks['commuting_gramians_do_not_imply_normal_operator'] = {
        'passed': True, 'commutator_of_gramians': dump_matrix(GL*GR-GR*GL),
        'normality_defect': dump_matrix(GL-GR)}

    examples = [sp.zeros(3), sp.eye(3), sp.Matrix([[1,2,0],[0,0,1],[0,0,0]]),
                sp.Matrix([[1,2,3],[2,4,6],[0,1,2]])]
    for A in examples:
        H = (A*A.T).pinv()
        M = A.T*H
        assert A*M*A == A and M*A*M == M and (A*M).T == A*M and (M*A).T == M*A
        assert M == A.pinv()
    checks['left_gramian_penrose_formula'] = {'passed': True, 'examples': len(examples)}

    T = sp.Matrix([[1, 1, 0], [0, 1, 1], [0, 0, 1]])
    A0 = sp.Matrix([[2, 0, 0], [0, 0, 1], [0, 0, 0]])
    A = T*A0*T.inv()
    D = T*sp.diag(sp.Rational(1,2),0,0)*T.inv()
    M = A.pinv()
    X = M*A*D*A*M
    C = A*A*D
    assert X*A*X == X and A*X*A == C
    assert (A*X)**2 == A*X and (X*A)**2 == X*A
    checks['cmp_recovers_core'] = {'passed': True, 'CMP': dump_matrix(X), 'core': dump_matrix(C)}

    N = sp.Matrix([[0,1,0],[0,0,1],[0,0,0]])
    B = sp.Matrix([[2,1,0],[1,0,1],[0,1,-1]])
    Q = sp.Matrix([[1,2,3],[4,5,6],[7,8,9]])
    W = stein(N, B, Q, 3)
    assert W-N*W*B == Q
    WL, WR = stein(N, N.T, sp.eye(3), 3), stein(N.T, N, sp.eye(3), 3)
    assert WL-N*WL*N.T == sp.eye(3) and WR-N.T*WR*N == sp.eye(3)
    assert WL.is_positive_definite and WR.is_positive_definite
    checks['finite_stein_one_sided_nilpotence'] = {
        'passed': True, 'left_gramian': dump_matrix(WL), 'right_gramian': dump_matrix(WR)}

    U = sp.Matrix([[sp.Rational(1,2),sp.Rational(1,4)],
                   [sp.Rational(1,3),sp.Rational(1,4)],
                   [sp.Rational(1,6),sp.Rational(1,2)]])
    V = sp.Matrix([[sp.Rational(1,4),sp.Rational(1,2),sp.Rational(3,4)],
                   [sp.Rational(3,4),sp.Rational(1,2),sp.Rational(1,4)]])
    S = sp.Matrix([[1,2,1],[2,1,3]])/10
    P = U*S*V.T
    assert P*sp.ones(2,1) == U*S*sp.ones(3,1)
    assert P.T*sp.ones(3,1) == V*S.T*sp.ones(2,1)
    assert sum(P) == sum(S) == 1
    checks['rectangular_triFactor_marginal_pushforward'] = {'passed': True, 'P': dump_matrix(P)}

    A = sp.ones(3)/3
    B = sp.ones(2)/2
    H, K = sp.eye(3)-A, sp.eye(2)-B
    L = sp.Matrix([[1,2],[4,-3],[5,7]])
    blocks = [A*L*B,H*L*B,A*L*K,H*L*K]
    assert sum(blocks, sp.zeros(3,2)) == L
    pair_values = [sp.trace(X.T*Y) for X,Y in itertools.combinations(blocks,2)]
    assert pair_values == [0]*6
    row_shift = sp.Matrix([1,3,-2])*sp.ones(1,2)
    col_shift = sp.ones(3,1)*sp.Matrix([[2,-7]])
    assert H*(L+row_shift+col_shift)*K == H*L*K
    checks['four_term_split_all_six_orthogonality_pairs'] = {'passed': True, 'pair_values': pair_values}

    a, c, b = sp.Matrix([sp.Rational(1,4),sp.Rational(3,4)]), \
              sp.Matrix([sp.Rational(3,4),sp.Rational(1,4)]), \
              sp.Matrix([sp.Rational(1,3),sp.Rational(2,3)])
    P1, P2 = a*b.T,c*b.T
    P = (P1+P2)/2
    assert P1 != P2 and all(x>0 for x in P1) and all(x>0 for x in P2)
    assert sum(P1)==sum(P2)==1 and P == (a+c)/2*b.T and P.det()==0
    checks['distinct_positive_two_peaks_remain_independent'] = {'passed': True, 'P': dump_matrix(P)}

    g = sp.symbols('w u1 u2 a1 a2 v1 v2 b1 b2')
    w,u1,u2,a1,a2,v1,v2,b1,b2 = g
    lhs=(w*u1*v1+(1-w)*a1*b1)*(w*u2*v2+(1-w)*a2*b2) - \
        (w*u1*v2+(1-w)*a1*b2)*(w*u2*v1+(1-w)*a2*b1)
    rhs=w*(1-w)*(u1*a2-a1*u2)*(v1*b2-b1*v2)
    assert sp.expand(lhs-rhs)==0
    checks['two_peak_minor_factorization'] = {'passed': True, 'symbolic_polynomial_identity': True}

    path = Path(__file__).resolve().parents[1]/'verification'/'exact_contract_regressions.json'
    path.write_text(json.dumps({'sympy_version': sp.__version__, 'kernel_verified': False,
                               'checks': checks}, indent=2, default=str))
    print(f'{len(checks)} exact contract regression groups passed.')

if __name__ == '__main__':
    main()
