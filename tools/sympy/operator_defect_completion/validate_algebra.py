"""Exact algebra checks only. This script does not elaborate or kernel-check Lean."""
from fractions import Fraction
import json
from pathlib import Path
import sympy as sp

# Free associative rational polynomials, with p*p=p as the sole extra relation.
# A tuple ('P', word) is a formal atom for an arbitrary linear readout.
def reduce_word(word):
    out = []
    for atom in word:
        if atom == 'p' and out and out[-1] == 'p':
            continue
        out.append(atom)
    return tuple(out)

class Poly:
    def __init__(self, terms=None):
        self.terms = {}
        for w, c in (terms or {}).items():
            w, c = reduce_word(w), Fraction(c)
            self.terms[w] = self.terms.get(w, Fraction()) + c
        self.terms = {w: c for w, c in self.terms.items() if c}
    def __add__(self, other):
        d = self.terms.copy()
        for w, c in other.terms.items():
            d[w] = d.get(w, Fraction()) + c
        return Poly(d)
    def __neg__(self):
        return Poly({w: -c for w, c in self.terms.items()})
    def __sub__(self, other):
        return self + -other
    def __mul__(self, other):
        d = {}
        for w, c in self.terms.items():
            for v, e in other.terms.items():
                t = reduce_word(w + v)
                d[t] = d.get(t, Fraction()) + c * e
        return Poly(d)
    def __eq__(self, other):
        return self.terms == other.terms

def atom(name):
    return Poly({(name,): 1})

def bracket(x, y):
    return x*y - y*x

def linear_readout(x):
    return Poly({(('P', w),): c for w, c in x.terms.items()})

one, zero = Poly({(): 1}), Poly()
p, x, y, z = map(atom, ('p', 'x', 'y', 'z'))
q = one-p
even = p*x*p + q*x*q
odd = p*x*q + q*x*p
checks = {}
def check(name, condition):
    if not condition:
        raise AssertionError(name)
    checks[name] = True

check('Peirce exact reconstruction', even+odd == x)
check('double commutator extracts odd part', bracket(p, bracket(p,x)) == odd)
check('upper corner square zero', (p*x*q)*(p*x*q) == zero)
check('lower corner square zero', (q*x*p)*(q*x*p) == zero)
check('compression bracket defect',
      p*bracket(x,y)*p-bracket(p*x*p,p*y*p) == p*x*q*y*p-p*y*q*x*p)
check('ambient Jacobi identity',
      bracket(x,bracket(y,z))+bracket(y,bracket(z,x))+bracket(z,bracket(x,y)) == zero)

def defect(x,y):
    return bracket(x,y)-linear_readout(bracket(x,y))
jac = (linear_readout(bracket(x,linear_readout(bracket(y,z))))
       +linear_readout(bracket(y,linear_readout(bracket(z,x))))
       +linear_readout(bracket(z,linear_readout(bracket(x,y)))))
feedback = -linear_readout(bracket(x,defect(y,z))+bracket(y,defect(z,x))+bracket(z,defect(x,y)))
check('projected Jacobiator exact feedback', jac == feedback)

# A full 4x4 noncommutative witness, conjugated so the retained idempotent is
# not diagonal. This is a regression, not a replacement for generic theorems.
U = sp.Matrix([[1,2],[3,4]])
V = sp.Matrix([[2,1],[0,1]])
S = sp.Matrix([[1,1,0,1],[0,1,1,0],[1,0,1,0],[0,0,1,1]])
assert S.det() != 0
Z, I = sp.zeros(2), sp.eye(2)
p0 = I.row_join(Z).col_join(Z.row_join(Z))
x0 = Z.row_join(U).col_join(Z.row_join(Z))
y0 = Z.row_join(Z).col_join(V.row_join(Z))
pM, XM, YM = (S*T*S.inv() for T in (p0,x0,y0))
qM = sp.eye(4)-pM
PM = lambda T: pM*T*qM+qM*T*pM
DM = XM*YM-YM*XM
check('witness coefficient blocks do not commute', U*V != V*U)
check('witness idempotent is non-diagonal', pM != sp.diag(*pM.diagonal()))
check('witness p squared equals p', pM*pM == pM)
check('witness retained X and Y', PM(XM)==XM and PM(YM)==YM)
check('witness nonzero defect is even, not odd', DM != sp.zeros(4) and PM(DM)==sp.zeros(4))
check('witness defect remains after reconstruction', DM-PM(DM)==DM)

report = {
    'checks_passed': len(checks),
    'checks': checks,
    'method': 'Exact rational free-associative polynomial reduction and exact rational matrix arithmetic',
    'extra_polynomial_relation': 'p*p=p',
    'lean_compilation_performed': False,
    'lean_axiom_audit_performed': False,
    'scope': 'Algebra identities and regression only; not a substitute for Lean elaboration or proof audit.'
}
Path(__file__).with_name('algebra_checks.json').write_text(json.dumps(report, indent=2)+'\n')
print(json.dumps(report, indent=2))
