#!/usr/bin/env python3
"""SymPy exact witnesses for the concrete `J₂(O_s)` scaling packet.

Lean owner:
  lean/InfoGeometry/Algebra/JordanCayleyInversionOs.lean

Scope:
  finite coordinate identities only for
  - trace-reversal involutivity,
  - determinant invariance under trace reversal,
  - integer/rational scalar scaling of the determinant formula.
"""
from __future__ import annotations

from dataclasses import dataclass
import sympy as sp


@dataclass(frozen=True)
class Zorn:
    a: sp.Expr
    b: sp.Expr
    x0: sp.Expr
    x1: sp.Expr
    x2: sp.Expr
    y0: sp.Expr
    y1: sp.Expr
    y2: sp.Expr

    def neg(self) -> "Zorn":
        return Zorn(*[-c for c in self.as_tuple()])

    def scale(self, r: sp.Expr) -> "Zorn":
        return Zorn(*[sp.expand(r * c) for c in self.as_tuple()])

    def detZ(self) -> sp.Expr:
        return sp.expand(self.a * self.b - (self.x0 * self.y0 + self.x1 * self.y1 + self.x2 * self.y2))

    def as_tuple(self):
        return (self.a, self.b, self.x0, self.x1, self.x2, self.y0, self.y1, self.y2)


@dataclass(frozen=True)
class Herm2x2Os:
    xp: sp.Expr
    xm: sp.Expr
    z: Zorn

    def trace_reversal(self) -> "Herm2x2Os":
        return Herm2x2Os(self.xm, self.xp, self.z.neg())

    def scale(self, r: sp.Expr) -> "Herm2x2Os":
        return Herm2x2Os(sp.expand(r * self.xp), sp.expand(r * self.xm), self.z.scale(r))

    def det(self) -> sp.Expr:
        return sp.expand(self.xp * self.xm - self.z.detZ())


r = sp.symbols('r')
xp, xm = sp.symbols('xp xm')
a, b, x0, x1, x2, y0, y1, y2 = sp.symbols('a b x0 x1 x2 y0 y1 y2')
X = Herm2x2Os(xp, xm, Zorn(a, b, x0, x1, x2, y0, y1, y2))

assert X.trace_reversal().trace_reversal() == X
assert sp.expand(X.trace_reversal().det() - X.det()) == 0
assert X.scale(r).trace_reversal() == X.trace_reversal().scale(r)
assert sp.expand(X.scale(r).det() - r**2 * X.det()) == 0

print('SYMPY_JORDAN_CAYLEY_OS_TRACE_REVERSAL_INVOLUTIVE_OK')
print('SYMPY_JORDAN_CAYLEY_OS_DET_TRACE_REVERSAL_OK')
print('SYMPY_JORDAN_CAYLEY_OS_TRACE_REVERSAL_SCALE_OK')
print('SYMPY_JORDAN_CAYLEY_OS_DET_SCALE_OK')
