#!/usr/bin/env python3
"""CAS derivation using the exact coordinate rows parsed from Lean.

This is deliberately symbolic.  It does not enumerate Boolean words.  Matrix
composition follows the carrier law `(g * h) X = h (g X)`, so a surface word
`p0 * ... * p5` is represented by the reversed column-matrix product.
"""
from pathlib import Path
import re
import sympy as sp

ROOT = Path(__file__).resolve().parents[1]
source = (ROOT / "lean/InfoGeometry/Algebra/Zorn/G2TwoSylowPCGenerators.lean").read_text()
names = ("a", "b", "x0", "x1", "x2", "y0", "y1", "y2")

def lean_rows(index):
    match = re.search(
        rf"def pc{index}Fun \(X : SplitOctF2\) : SplitOctF2 :=\s*⟨(.*?)⟩",
        source, re.S)
    assert match, index
    fields = [x.strip() for x in match.group(1).split(",")]
    assert len(fields) == 8
    rows = []
    for field in fields:
        terms = [x.strip() for x in field.split("^^")]
        parity = {name: terms.count(f"X.{name}") % 2 for name in names}
        assert all(term in {f"X.{name}" for name in names} for term in terms), field
        rows.append([parity[name] for name in names])
    return rows

e = sp.symbols("e0:6")
f = sp.symbols("f0:6")
vars = e + f
I = [[int(i == j) for j in range(8)] for i in range(8)]
gens = [lean_rows(i) for i in range(1, 7)]

def red(x):
    p = sp.Poly(sp.expand(x), *vars, modulus=2)
    result = 0
    for mon, coeff in p.terms():
        if int(coeff) & 1:
            term = 1
            for v, power in zip(vars, mon):
                if power:
                    term *= v
            result += term
    return sp.Poly(result, *vars, modulus=2).as_expr()

def mm(a, b):
    return [[red(sum(a[i][k] * b[k][j] for k in range(8)))
             for j in range(8)] for i in range(8)]

def factor(a, q):
    return [[red(I[i][j] + q * (a[i][j] + I[i][j]))
             for j in range(8)] for i in range(8)]

def word(bits):
    out = I
    for k in range(6):
        out = mm(factor(gens[k], bits[k]), out)
    return out

def xor(*terms):
    return red(sum(terms, sp.Integer(0)))

def and_(*terms):
    out = sp.Integer(1)
    for term in terms:
        out = red(out * term)
    return out

def pc_combine(e_bits, f_bits):
    return [
        xor(e_bits[0], f_bits[0]),
        xor(e_bits[1], f_bits[1]),
        xor(and_(e_bits[1], f_bits[0]), e_bits[2], f_bits[2]),
        xor(and_(e_bits[1], f_bits[0]), e_bits[3],
                and_(e_bits[4], f_bits[0]), f_bits[3]),
        xor(e_bits[4], f_bits[4]),
        xor(and_(e_bits[1], e_bits[2], f_bits[0]),
            and_(e_bits[1], f_bits[0], f_bits[1]),
            and_(e_bits[1], f_bits[0], f_bits[2]),
            and_(e_bits[1], f_bits[0]),
            and_(e_bits[1], f_bits[1]),
            and_(e_bits[2], f_bits[0]),
            and_(e_bits[2], f_bits[2]),
            and_(e_bits[3], f_bits[1]),
            and_(e_bits[4], f_bits[0], f_bits[1]),
            and_(e_bits[4], f_bits[1]),
            and_(e_bits[4], f_bits[2]),
            e_bits[5], f_bits[5]),
    ]

inverses = [sp.Matrix(a).inv_mod(2).tolist() for a in gens]

def inv(a):
    for original, inverse in zip(gens, inverses):
        if original == a:
            return inverse
    raise AssertionError("unknown generator")

def peel(M, k, pivot):
    return mm(M, factor(inv(gens[k]), pivot))

def recover(M):
    p0 = M[2][7]
    M1 = peel(M, 0, p0)
    p1 = M1[3][2]
    M2 = peel(M1, 1, p1)
    p2 = M2[3][7]
    M3 = peel(M2, 2, p2)
    p4 = M3[6][2]
    p3 = red(M3[4][3] + p4)
    M4 = peel(M3, 3, p3)
    M5 = peel(M4, 4, p4)
    p5 = M5[4][2]
    M6 = peel(M5, 5, p5)
    assert all(red(M6[i][j] - I[i][j]) == 0
               for i in range(8) for j in range(8))
    return [p0, p1, p2, p3, p4, p5]

product = recover(mm(word(f), word(e)))
inverse_matrix = I
for k in range(6):
    inverse_matrix = mm(inverse_matrix, factor(inverses[k], e[k]))
inverse = recover(inverse_matrix)
print("LEAN_COORDINATE_ROWS=PASS")
print("PC_MATRIX_CERTIFICATE_BEGIN")
for index, matrix in enumerate(gens, start=1):
    print(f"pc{index}=")
    for row in matrix:
        print("".join(str(bit) for bit in row))
print("PC_MATRIX_CERTIFICATE_END")
for i, value in enumerate(product):
    print(f"g{i}={sp.Poly(value, *vars, modulus=2).as_expr()}")
for i, value in enumerate(inverse):
    print(f"q{i}={sp.Poly(value, *e, modulus=2).as_expr()}")
assert all(red(x.subs({v: 0 for v in f}) - e[i]) == 0
           for i, x in enumerate(product))
assert all(red(x.subs({v: 0 for v in e}) - f[i]) == 0
           for i, x in enumerate(product))
print("LEAN_ORIENTED_PC_NORMAL_FORM=PASS")
print("NO_ASSIGNMENT_ENUMERATION=PASS")

closure_matrix = mm(word(f), word(e))
closure_expected = word(pc_combine(e, f))
assert all(red(closure_matrix[i][j] - closure_expected[i][j]) == 0
           for i in range(8) for j in range(8))
print("LEAN_ORIENTED_PC_CLOSURE_MATRIX=PASS")

zero_generator = [sp.Integer(1), 0, 0, 0, 0, 0]
zero_transport = recover(mm(word(zero_generator), word(e)))
zero_expected = pc_combine(e, zero_generator)
assert all(red(zero_transport[i] - zero_expected[i]) == 0
           for i in range(6))
print("PC_WORD_ONE_AT_ZERO_TRUE_TRANSPORT=PASS")
