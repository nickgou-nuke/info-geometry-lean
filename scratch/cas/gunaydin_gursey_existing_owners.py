#!/usr/bin/env python3
"""Exact, source-aligned audit; CAS evidence, NOT a Lean proof.

Run from any directory; emits deterministic JSON to stdout, never edits owners.
Reuse the existing Zorn product and full derivation-equation constructor.
Read the existing Lean parameter action, finite matrices and structure constants
rather than silently replacing them by a guessed G2 basis. The deliberately
small arithmetic reader rejects syntax outside its supported fragment.

CAS coordinates: (a,b,u0,u1,u2,v0,v1,v2), column vectors, AB = A after B.
Lean vector-Zorn fields: (a,v,w,b), where v=upper u and w=lower v.
Native matrix export: (a,u0,u1,u2,b,v0,v1,v2).
All arithmetic is exact over QQ; polynomial residuals are over ZZ.
"""
from __future__ import annotations

import ast
import hashlib
import importlib.util
import json
from pathlib import Path
import re
import sys

import sympy as s

ROOT = Path(__file__).resolve().parents[2]
SOURCES: dict[str, str] = {}
CHECKS: dict[str, object] = {}


def source(path: str) -> str:
    text = (ROOT / path).read_text()
    SOURCES[path] = hashlib.sha256(text.encode()).hexdigest()
    return text


def load(path: str, name: str):
    source(path)
    spec = importlib.util.spec_from_file_location(name, ROOT / path)
    assert spec is not None and spec.loader is not None
    module = importlib.util.module_from_spec(spec)
    sys.modules[name] = module
    spec.loader.exec_module(module)
    return module


def arithmetic(text: str, names: dict[str, s.Expr] | None = None) -> s.Expr:
    """No eval: only names, integer constants and rational arithmetic."""
    names = names or {}
    text = re.sub(r'\s*:\s*ℚ', '', text)
    node = ast.parse(' '.join(text.split()), mode='eval').body

    def visit(n):
        if isinstance(n, ast.Constant) and type(n.value) is int:
            return s.Integer(n.value)
        if isinstance(n, ast.Name) and n.id in names:
            return names[n.id]
        if isinstance(n, ast.UnaryOp) and isinstance(n.op, ast.USub):
            return -visit(n.operand)
        if isinstance(n, ast.BinOp):
            a, b = visit(n.left), visit(n.right)
            if isinstance(n.op, ast.Add): return a + b
            if isinstance(n.op, ast.Sub): return a - b
            if isinstance(n.op, ast.Mult): return a * b
            if isinstance(n.op, ast.Div): return a / b
        raise ValueError(f'Unsupported arithmetic: {ast.dump(n)}')

    return visit(node)


def matrices(text: str) -> list[s.Matrix]:
    return [s.Matrix([[arithmetic(c) for c in row.split(',')]
                      for row in body.split(';')])
            for body in re.findall(r'!!\[([^\]]+)\]', text)]


def action_from_source(text: str, name: str) -> s.Matrix:
    """Extract eight polynomial coordinates from the actual Lean definition."""
    body = text.split(f'def {name} ', 1)[1].split(':=', 1)[1]
    body = body.split('⟨', 1)[1].split('⟩', 1)[0]
    fields = body.split(',')
    assert len(fields) == 4
    vecs = []
    for field in fields[1:3]:
        m = re.fullmatch(r'\s*fun i => if i = 0 then\s+(.*?)else if i = 1 then\s+(.*?)else(.*)',
                         field, re.S)
        assert m is not None
        vecs.extend(m.groups())
    expressions = [fields[0], fields[3], *vecs]
    p = s.symbols('p0:14')
    x = s.symbols('x0:8')
    names = {str(t): t for t in (*p, *x)}
    parsed = []
    for expr in expressions:
        expr = re.sub(r'p\s+(\d+)', r'p\1', expr)
        expr = re.sub(r'X\.v\s+(\d+)', lambda m: f'x{2 + int(m[1])}', expr)
        expr = re.sub(r'X\.w\s+(\d+)', lambda m: f'x{5 + int(m[1])}', expr)
        expr = expr.replace('X.a', 'x0').replace('X.b', 'x1')
        parsed.append(s.expand(arithmetic(expr, names)))
    D = s.Matrix([[expr.coeff(t) for t in x] for expr in parsed])
    assert (D * s.Matrix(x) - s.Matrix(parsed)).applyfunc(s.expand) == s.zeros(8, 1)
    return D


def off_from_source(text: str) -> s.Matrix:
    body = text.split('def offDiagonalAction ', 1)[1].split(':=', 1)[1]
    fields = body.split('⟨', 1)[1].split('⟩', 1)[0].split(',')
    assert len(fields) == 4
    x = s.symbols('x0:8')
    p, q = s.Matrix(s.symbols('p0:3')), s.Matrix(s.symbols('q0:3'))
    vectors = {'p': p, 'q': q, 'v': s.Matrix(x[2:5]), 'w': s.Matrix(x[5:8])}
    names = {str(t): t for t in (*x, *p, *q)}
    expressions = [fields[0], fields[3]]
    for field in fields[1:3]:
        assert field.strip().startswith('fun i =>')
        expressions.extend(re.sub(r'\bi\b', str(i), field.split('=>', 1)[1]) for i in range(3))
    result = []
    for expr in expressions:
        def dot(m):
            name = f'dot_{m[1]}_{m[2]}'
            names[name] = vectors[m[1]].dot(vectors[m[2]])
            return name
        def cross(m):
            name = f'cross_{m[1]}_{m[2]}_{m[3]}'
            names[name] = vectors[m[1]].cross(vectors[m[2]])[int(m[3])]
            return name
        expr = re.sub(r'ZornVec3.dot ([pq]) X\.([vw])', dot, expr)
        expr = re.sub(r'ZornVec3.cross ([pq]) X\.([vw]) (\d)', cross, expr)
        expr = re.sub(r'([pq])\s+(\d)', r'\1\2', expr)
        expr = expr.replace('X.a', 'x0').replace('X.b', 'x1')
        result.append(s.expand(arithmetic(expr, names)))
    return s.Matrix(result)


def flat(M): return s.Matrix(list(M))
def comm(A, B): return A * B - B * A


def main():
    legacy = load('tools/sympy/split_octonion_derivation_classification.py', 'gg_derivation_audit')
    mult = legacy.mult
    source('tools/sympy/split_octonion_multiplication.py')
    source('lean/InfoGeometry/Algebra/ZornVectorMatrix.lean')
    dim = source('lean/InfoGeometry/Lie/CanonicalZornDerivationDimension.lean')
    export = source('lean/InfoGeometry/Lie/CanonicalZornG2NativeMatrixExport.lean')
    data = source('lean/InfoGeometry/Lie/CanonicalZornG2CASData.lean')
    align = source('lean/InfoGeometry/Lie/CanonicalZornG2BasisAlignment.lean')
    for path in ['Lie/CanonicalZornPeirceSL3Bridge', 'Lie/CanonicalZornG2CASReplay',
                 'Lie/SplitOctonionCliffordAction', 'Algebra/AlternativeDerivations',
                 'Exceptional/CompositionTriality', 'Exceptional/CompositionTrialityAlternativeBridge']:
        source(f'lean/InfoGeometry/{path}.lean')

    # Re-run the existing multiplication checks, including symbolic norm composition.
    mult.verify_basis_table()
    mult.verify_nonassoc_and_alternativity_on_basis()
    mult.verify_symbolic_norm_composition()
    CHECKS['existing_multiplication_checks'] = 'PASS'
    basis = legacy.BASIS
    vec = lambda z: s.Matrix(legacy.coords(z))
    zv = lambda v: legacy.from_coords(list(v))
    prod = lambda x, y: vec(zv(x) * zv(y))
    T = [[vec(x * y) for y in basis] for x in basis]
    left = [s.Matrix.hstack(*row) for row in T]
    right = [s.Matrix.hstack(*(T[j][i] for j in range(8))) for i in range(8)]
    L = lambda v: sum((v[i] * left[i] for i in range(8)), s.zeros(8))
    R = lambda v: sum((v[i] * right[i] for i in range(8)), s.zeros(8))
    for i in range(8):
        for j in range(8):
            assert left[i] * left[j] + left[j] * left[i] == L(T[i][j] + T[j][i])
            assert right[i] * right[j] + right[j] * right[i] == R(T[i][j] + T[j][i])
    CHECKS['polarized_alternativity'] = {'left_operator_pairs': 64, 'right_operator_pairs': 64}

    D = action_from_source(dim, 'parameterAction')
    assert D == action_from_source(export, 'rationalParameterAction')
    p = s.symbols('p0:14')
    native = [D.diff(t) for t in p]
    assert D == sum((p[i] * native[i] for i in range(14)), s.zeros(8))
    A = legacy.build_derivation_constraint_matrix()
    B = s.Matrix.hstack(*(flat(M) for M in native))
    assert A.shape == (512, 64) and A.rank() == 50
    assert B.rank() == 14 and A * B == s.zeros(512, 14)
    G = s.zeros(8)
    G[0, 1] = G[1, 0] = 1
    for i in range(3): G[2+i, 5+i] = G[5+i, 2+i] = -1
    trace = s.Matrix([[1, 1, 0, 0, 0, 0, 0, 0]])
    for M in native:
        assert M.T * G + G * M == s.zeros(8)
        assert trace * M == s.zeros(1, 8)
        assert M * vec(mult.ONE) == s.zeros(8, 1)
    E = s.Matrix.hstack(*(M[:, 0] for M in native))
    assert E.rank() == 6
    assert all(M[:, 1] == -M[:, 0] for M in native)
    stab = [sum((v[i] * native[i] for i in range(14)), s.zeros(8)) for v in E.nullspace()]
    for M in stab:
        N = M[2:5, 2:5]
        assert s.trace(N) == 0 and M[5:8, 5:8] == -N.T
        expected = s.zeros(8)
        expected[2:5, 2:5], expected[5:8, 5:8] = N, -N.T
        assert M == expected
    CHECKS['native_derivations'] = {'rank': 14, 'constraint_rank': 50,
        'basis_product_checks': 14 * 64, 'norm_skew_trace_unit': 'PASS',
        'peirce_stabilizer_dimension': 8, 'stabilizer_is_sl3_block_action_over_QQ': 'PASS',
        'rational_real_action_source_agreement': 'PASS'}

    # Cross-product trace identity: exact polynomial identity, not random vectors.
    m = s.Matrix(3, 3, s.symbols('m0:9'))
    x, y = s.Matrix(s.symbols('x0:3')), s.Matrix(s.symbols('y0:3'))
    assert ((m*x).cross(y) + x.cross(m*y) + m.T*x.cross(y) - s.trace(m)*x.cross(y)).applyfunc(s.expand) == s.zeros(3, 1)
    CHECKS['cross_product_trace_identity'] = 'PASS'

    # Parse and check all stored rational matrices and bracket coefficients.
    permutation = s.eye(8)[[0, 2, 3, 4, 1, 5, 6, 7], :]
    native_reordered = [permutation * M * permutation.T for M in native]
    frame = matrices(export.split('have hframe :', 1)[1])[0]
    inv = matrices(export.split('def explicitInverseMatrix', 1)[1])[0]
    assert frame * inv == inv * frame == s.eye(8)
    tables = matrices(export.split('def rootDerivationRationalTable', 1)[1].split('set_option', 1)[0])
    cas = matrices(data.split('def casStructureConstant', 1)[0])
    P = matrices(align.split('def casToNativeBasis ', 1)[1])[0]
    assert len(tables) == len(cas) == 14 and P.det() != 0
    for i in range(14):
        assert tables[i] == inv * native_reordered[i] * frame
        assert cas[i] == sum((P[j, i] * native_reordered[j] for j in range(14)), s.zeros(8))
    entries = re.findall(r'\| \((\d+), (\d+), (\d+)\) => (-?\d+)', data)
    constants = {(int(i), int(j), int(k)): int(c) for i, j, k, c in entries}
    assert len(constants) == len(entries)
    for i in range(14):
        for j in range(14):
            assert comm(cas[i], cas[j]) == sum((constants.get((i,j,k), 0) * cas[k] for k in range(14)), s.zeros(8))
    CHECKS['stored_CAS_tables'] = {'circular_matrices': 14, 'aligned_CAS_matrices': 14,
        'full_operator_brackets': 196, 'nonzero_structure_constants': len(constants),
        'frame_inverse_and_signed_basis_alignment': 'PASS'}

    # Full imaginary split Clifford signature: H, U_i+V_i, U_i-V_i.
    imag = [vec(mult.EPLUS - mult.EMINUS)] + [vec(mult.UP[i] + mult.DOWN[i]) for i in range(3)] + [vec(mult.UP[i] - mult.DOWN[i]) for i in range(3)]
    signs = [1, 1, 1, 1, -1, -1, -1]
    for i in range(7):
        assert L(imag[i])**2 == signs[i] * s.eye(8)
        for j in range(7):
            assert L(imag[i])*L(imag[j]) + L(imag[j])*L(imag[i]) == (2*signs[i] if i == j else 0)*s.eye(8)
    CHECKS['imaginary_left_clifford'] = {'operator_pairs': 49, 'signature_positive_negative': [4, 3]}

    # Triality order matches CompositionTriality: output, left, right.
    rows = {}
    for i in range(8):
        for j in range(8):
            for k in range(8):
                row = (8*i+j)*8+k
                for a in range(8):
                    for col, value in [(k*8+a, T[i][j][a]),
                                       (64+a*8+i, -T[a][j][k]),
                                       (128+a*8+j, -T[i][a][k])]:
                        if value: rows[row, col] = rows.get((row, col), 0) + value
    trial = s.SparseMatrix(512, 192, rows)
    null = trial.nullspace()
    assert len(null) == 30
    triples = [[s.Matrix(8, 8, list(v[64*t:64*(t+1)])) for t in range(3)] for v in null]
    for t in triples:
        for u in triples:
            bracket = s.SparseMatrix.vstack(*(s.SparseMatrix(flat(comm(t[k], u[k]))) for k in range(3)))
            assert trial * bracket == s.zeros(512, 1)
    skew_rows = []
    for t in range(3):
        for i in range(8):
            for j in range(8):
                row = [0]*192
                for k in range(8):
                    row[64*t+k*8+i] += G[k,j]
                    row[64*t+k*8+j] += G[i,k]
                skew_rows.append(row)
    skew_trial = trial.col_join(s.SparseMatrix(skew_rows))
    assert skew_trial.rank() == 164
    diagonal = s.Matrix.vstack(s.eye(64), s.eye(64), s.eye(64))
    assert trial * diagonal == A
    CHECKS['local_triality'] = {'linear_triple_dimension_over_QQ': 30,
        'norm_skew_triple_dimension_over_QQ': 28, 'commutator_pairs': 900,
        'diagonal_equations_equal_derivation_equations': 'PASS'}

    # User's supplied signs: deliberately compare, never promote to an owner.
    def off(p, q, X, corrected=False):
        a, b, u, v = X[0], X[1], s.Matrix(X[2:5]), s.Matrix(X[5:8])
        scalar = p.dot(v) - q.dot(u)
        if corrected:
            return s.Matrix([-scalar, scalar, *((a-b)*p-q.cross(v)), *((b-a)*q+p.cross(u))])
        return s.Matrix([scalar, -scalar, *((a-b)*p+q.cross(v)), *((b-a)*q-p.cross(u))])
    unit3 = [s.eye(3)[:, i] for i in range(3)]
    zero3 = s.zeros(3, 1)
    bad = lambda X: off(unit3[0], zero3, X)
    e, v = vec(mult.EPLUS), vec(mult.DOWN[0])
    lhs, rhs = bad(prod(e,v)), prod(bad(e),v) + prod(e,bad(v))
    assert lhs == s.zeros(8, 1) and rhs == 2*e
    assert (bad(e).T*G*v + e.T*G*bad(v))[0] == -2
    h = vec(mult.EPLUS-mult.EMINUS)
    bad_comm = off(unit3[0],zero3,off(unit3[1],zero3,h))-off(unit3[1],zero3,off(unit3[0],zero3,h))
    bad_target = off(zero3,-unit3[2],h)
    assert bad_comm == -4*vec(mult.DOWN[2]) and bad_target == 2*vec(mult.DOWN[2])
    corrected = lambda p,q: s.Matrix.hstack(*(off(p,q,vec(b),True) for b in basis))
    for i in range(3):
        for j in range(3):
            assert comm(corrected(unit3[i],zero3),corrected(unit3[j],zero3)) == corrected(zero3,-2*unit3[i].cross(unit3[j]))
        for M in [corrected(unit3[i],zero3),corrected(zero3,unit3[i])]:
            assert A*flat(M) == s.zeros(512,1) and M.T*G+G*M == s.zeros(8)
    off_source = source('lean/InfoGeometry/Algebra/Zorn/OffDiagonalDerivation.lean')
    off_expr = off_from_source(off_source)
    symbolic_x = s.Matrix(s.symbols('x0:8'))
    symbolic_p, symbolic_q = s.Matrix(s.symbols('p0:3')), s.Matrix(s.symbols('q0:3'))
    assert (off_expr + off(symbolic_p, symbolic_q, symbolic_x, True)).applyfunc(s.expand) == s.zeros(8, 1)
    owner_matrix = off_expr.jacobian(symbolic_x)
    assert (owner_matrix.T*G+G*owner_matrix).applyfunc(s.expand) == s.zeros(8)
    for i in range(3):
        for j in range(3):
            assert comm(-corrected(zero3,unit3[i]),-corrected(zero3,unit3[j])) == -corrected(-2*unit3[i].cross(unit3[j]),zero3)
    evaluations = s.Matrix.hstack(*[(-corrected(v,zero3))[:,0] for v in unit3],
                                  *[(-corrected(zero3,v))[:,0] for v in unit3])
    assert evaluations.rank() == 6
    t = s.Symbol('t')
    norm = lambda v: (v.T*G*v)[0]/2
    assert s.expand(norm(symbolic_x+t*off_expr)-norm(symbolic_x)-t**2*norm(off_expr)) == 0
    CHECKS['existing_off_diagonal_owner'] = {
        'source_parsed_sign_alignment': 'PASS', 'basis_generators': 6,
        'leibniz_norm_skew': 'PASS', 'full_upper_brackets': 9, 'full_lower_brackets': 9,
        'parameter_injectivity_rank': 6, 'quadratic_norm_expansion': 'PASS',
        'bracket_q_coefficient_in_owner_normalization': 2,
        'relation_to_corrected_prompt_scalar_terms_convention': 'negative of corrected operator'}
    CHECKS['prompt_formula_counterexamples'] = {
        'D_E11_times_V0': list(map(int,lhs)), 'Leibniz_RHS': list(map(int,rhs)),
        'norm_skew_residual': -2, 'proposed_commutator_on_H_lower_V2': -4,
        'proposed_RHS_on_H_lower_V2': 2,
        'corrected_off_diagonal_generators_6': 'PASS',
        'corrected_p_p_bracket_q_coefficient': -2}
    # Independent exact linear algebra engine, on the identical constraint matrices.
    from sage.all import QQ, matrix
    from sage.env import SAGE_VERSION
    sage_rank = lambda M: int(matrix(QQ, [[int(c) for c in row] for row in M.tolist()]).rank())
    ranks = {'derivation_constraints': sage_rank(A), 'native_generators': sage_rank(B),
             'peirce_evaluation': sage_rank(E), 'triality_constraints': sage_rank(trial),
             'skew_triality_constraints': sage_rank(skew_trial)}
    assert ranks == {'derivation_constraints': 50, 'native_generators': 14,
                     'peirce_evaluation': 6, 'triality_constraints': 162,
                     'skew_triality_constraints': 164}
    CHECKS['independent_Sage_QQ_ranks'] = {'sage_version': SAGE_VERSION, **ranks}
    source('scratch/cas/gunaydin_gursey_existing_owners.py')
    print(json.dumps({'object': 'existing_split_octonion_derivation_clifford_triality_audit',
        'authority': 'exact CAS evidence, not kernel certification or paper authentication',
        'ring': 'QQ; expanded polynomial identities have integer coefficients',
        'basis': legacy.BASIS_NAMES, 'operator_convention': 'column images; AB=A after B',
        'source_sha256': SOURCES, 'sympy_version': s.__version__, 'checks': CHECKS},
        sort_keys=True, indent=2))


if __name__ == '__main__':
    main()
