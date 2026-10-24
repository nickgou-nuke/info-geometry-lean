#!/usr/bin/env python3
"""Exact supplementary audit of the native Zorn color operator conventions.

Columns are images of (E11,E22,U0,U1,U2,V0,V1,V2); AB means A after B.
Q=L(U), C=-L(V). This is computational evidence, not a Lean proof or a paper
attribution. Universal statements are proved in the source-hashed Lean owners.
Run with a Python interpreter providing SymPy; no dependency updates required.
"""
import hashlib
import importlib.util
import json
from pathlib import Path
import sys
import sympy as s

ROOT = Path(__file__).resolve().parents[1]
SOURCE = ROOT / 'tools/sympy/split_octonion_multiplication.py'
spec = importlib.util.spec_from_file_location('zorn_color_cas', SOURCE)
z = importlib.util.module_from_spec(spec)
sys.modules[spec.name] = z
spec.loader.exec_module(z)


def coords(x):
    return s.Matrix([x.a, x.b, *x.x, *x.y])


def left(x):
    return s.Matrix.hstack(*(coords(x*y) for y in z.BASIS))


def comm(a, b):
    return a*b-b*a


def anti(a, b):
    return a*b+b*a


def rank(matrices):
    return s.Matrix.hstack(*(m.reshape(m.rows*m.cols, 1) for m in matrices)).rank()


I, O = s.eye(8), s.zeros(8)
Q, C = [left(x) for x in z.UP], [-left(x) for x in z.DOWN]
G = [comm(C[i], Q[i]) for i in range(3)]
P, gamma = left(z.EPLUS), left(z.EPLUS-z.EMINUS)
assert G[0]*G[1]*G[2] == gamma == 2*P-I
assert gamma == s.diag(1, -1, 1, 1, 1, -1, -1, -1)
for i in range(3):
    assert Q[i]*Q[i] == C[i]*C[i] == O
    assert G[i] == I+2*C[i]*Q[i] and G[i]*G[i] == I
    for j in range(3):
        assert anti(Q[i], Q[j]) == anti(C[i], C[j]) == O
        assert anti(Q[i], C[j]) == (-I if i == j else O)
        assert comm(G[i], G[j]) == O
    for x in [Q[i], C[i]]:
        assert anti(gamma, x) == O and anti(P, x) == x
E = [[-Q[i]*C[j] for j in range(3)] for i in range(3)]
for i in range(3):
    for j in range(3):
        assert comm(gamma, E[i][j]) == comm(P, E[i][j]) == O
        for k in range(3):
            assert comm(E[i][j], Q[k]) == (Q[i] if j == k else O)
            assert comm(E[i][j], C[k]) == (-C[j] if i == k else O)
            for m in range(3):
                assert comm(E[i][j], E[k][m]) == (
                    (E[i][m] if j == k else O)-(E[k][j] if m == i else O))
plus, minus = [Q[i]-C[i] for i in range(3)], [Q[i]+C[i] for i in range(3)]
for i in range(3):
    assert plus[i]*plus[i] == I and minus[i]*minus[i] == -I
    assert G[i] == minus[i]*plus[i]
    assert G[i]*plus[i] == minus[i] and G[i]*minus[i] == plus[i]
    for j in range(3):
        assert anti(plus[i], minus[j]) == O
        if i != j:
            rotation = plus[i]*plus[j]-minus[i]*minus[j]
            for k in range(3):
                for family in [plus, minus]:
                    assert comm(rotation, family[k]) == 2*(
                        (family[i] if j == k else O)-(family[j] if i == k else O))
tp, tm = sum(plus, O), sum(minus, O)
assert tp*tp == 3*I and tm*tm == -3*I and anti(tp, tm) == O
odd = Q+C
assert rank([anti(x, y) for x in odd for y in odd]) == 1
assert rank([I]+[e for row in E for e in row]) == 10
assert rank(odd) == 6
assert rank([I]+[e for row in E for e in row]+odd) == 16
wrongP = s.diag(0, 1, 1, 1, 1, 0, 0, 0)
assert (anti(wrongP, Q[0])-Q[0])*coords(z.EMINUS) == coords(z.UP[0])


def unit(i, j):
    matrix = s.zeros(4)
    matrix[i, j] = 1
    return matrix


standard_odd = [unit(i, 3) for i in range(3)]+[unit(3, i) for i in range(3)]
assert rank([anti(x, y) for x in standard_odd for y in standard_odd]) == 9
assert comm(anti(unit(0, 3), unit(3, 1)), unit(0, 0)) == -unit(0, 1)
owners = ['ZornVectorMatrix', 'ZornSignedCAR', 'ZornLeftGrading', 'ZornLeftParity',
          'ZornLeftMajorana', 'ZornMajoranaRotations', 'ZornColorBilinears',
          'ZornRightProjectionObstruction', 'ZornColorOperatorCoordinates',
          'ZornColorOperatorClosure', 'ZornColorOddDerived', 'ZornColorGL31Obstruction']
paths = [ROOT / f'lean/InfoGeometry/Algebra/{name}.lean' for name in owners]
paths += [SOURCE, Path(__file__).resolve()]
print(json.dumps({
    'arithmetic': 'exact integers and rational rank; SymPy '+s.__version__,
    'basis': ['E11', 'E22', 'U0', 'U1', 'U2', 'V0', 'V1', 'V2'],
    'matrix_orientation': 'columns; AB = A after B',
    'signed_dual': 'Q=L(U), C=-L(V); not an asserted Hilbert adjoint',
    'grading_diagonal': list(map(int, gamma.diagonal())),
    'even_odd_total_dimensions': [10, 6, 16],
    'odd_derived_dimension': 1, 'standard_gl31_odd_derived_dimension': 9,
    'CAR_color_bilinears_Majorana_rotations_collective_squares': 'PASS',
    'wrong_projector_counterexample': 'PASS',
    'gl31_noncentral_odd_bracket': 'PASS',
    'proof_boundary': 'Supplementary CAS; kernel-checked Lean owners establish universal results',
    'source_sha256': {str(p.relative_to(ROOT)): hashlib.sha256(p.read_bytes()).hexdigest()
                      for p in paths}}, sort_keys=True, indent=2))
