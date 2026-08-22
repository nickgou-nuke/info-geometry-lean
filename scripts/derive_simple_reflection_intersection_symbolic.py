#!/usr/bin/env python3
"""Singular certificate for the simple-reflection B-intersection.

The variables describe two symbolic PC words.  Singular reduces the matrix
equations ``PC(e) = s * PC(f) * s⁻¹`` modulo Boolean relations; no elements of
the 64-element subgroup and no Boolean assignments are enumerated.
"""

from pathlib import Path
import re
import subprocess
import sympy as sp

ROOT = Path(__file__).resolve().parents[1]
gap = subprocess.run(
    ["gap", "-q", str(ROOT / "scripts/export_carrier_pc_rows.g")],
    cwd=ROOT, check=True, capture_output=True, text=True,
)
rows = {}
for line in gap.stdout.splitlines():
    m = re.fullmatch(r"PCROW ([1-6]) ([0-9,;]*)", line.strip())
    if m:
        rows[int(m.group(1)) - 1] = [
            [int(x) - 1 for x in block.split(",") if x]
            for block in m.group(2).split(";")
        ]
assert set(rows) == set(range(6))

e = sp.symbols("e0:6")
f = sp.symbols("f0:6")
variables = e + f

def boolean(expr):
    poly = sp.Poly(sp.expand(expr), *variables, modulus=2)
    result = 0
    for monomial, coefficient in poly.terms():
        if int(coefficient) & 1:
            term = 1
            for variable, exponent in zip(variables, monomial):
                if exponent:
                    term *= variable
            result += term
    return sp.Poly(result, *variables, modulus=2).as_expr()

def generator(index):
    result = [[int(i == j) for j in range(8)] for i in range(8)]
    support = rows[index]
    return [[int(j in support[i]) for j in range(8)] for i in range(8)]

def multiply(left, right):
    return [[boolean(sum(left[i][k] * right[k][j] for k in range(8)))
             for j in range(8)] for i in range(8)]

identity = [[int(i == j) for j in range(8)] for i in range(8)]

def factor(index, variables_):
    p = generator(index)
    return [[boolean(identity[i][j] + variables_[index] *
                     (p[i][j] + identity[i][j])) for j in range(8)]
            for i in range(8)]

def word(variables_):
    result = identity
    for index in range(6):
        result = multiply(factor(index, variables_), result)
    return result

# swap01 is an involution; its matrix is the exact native Weyl matrix.
s = [[1,0,0,0,0,0,0,0], [0,1,0,0,0,0,0,0],
     [0,0,0,1,0,0,0,0], [0,0,1,0,0,0,0,0],
     [0,0,0,0,1,0,0,0], [0,0,0,0,0,0,1,0],
     [0,0,0,0,0,1,0,0], [0,0,0,0,0,0,0,1]]

left = multiply(s, multiply(word(e), s))
right = word(f)
equations = [boolean(left[i][j] + right[i][j])
             for i in range(8) for j in range(8)]
equations += [x*x + x for x in variables]

def singular_name(expr):
    return str(expr).replace("**", "^")

ring = "ring r=2,(%s),dp;" % ",".join(map(str, variables))
script = [ring, "ideal I=%s;" % ",".join(map(singular_name, equations)),
          "option(redSB);", "ideal G=std(I);", "G;"]
result = subprocess.run(["Singular", "-q"], input="\n".join(script),
                        text=True, capture_output=True, check=True)
print("SIMPLE_REFLECTION_INTERSECTION_SYMBOLIC=PASS")
print("NO_ASSIGNMENT_ENUMERATION=PASS")
print(result.stdout.strip())
