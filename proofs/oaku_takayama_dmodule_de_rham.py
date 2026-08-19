#!/usr/bin/env python3
"""SymPy witness for Oaku--Takayama math/9801114.

The paper's algorithm computes de Rham cohomology of
U = C^n \\ V(f) by translating O_X[1/f] to a finitely generated Weyl
algebra module, Fourier transforming, resolving, and restricting/integrating.

This script checks the introductory A_1 Weyl-algebra example from the paper:

  p = (x-u)(x-v) d - a(x-v) - b(x-u)

under the formal Fourier transform x |-> -d, d |-> x, with [d,x]=1.
The normal form should be

  p_hat = x d^2 + ((u+v)x + 2+a+b)d + uv x + u+v+av+bu.

It also records the indicial/b-polynomial b(s)=s(s-a-b).
"""

from __future__ import annotations

from dataclasses import dataclass
from math import comb, prod
from typing import Dict, Tuple

import sympy as sp

Monomial = Tuple[int, int]  # x^i d^j, normally ordered


def falling(n: int, r: int) -> int:
    if r == 0:
        return 1
    return prod(n - k for k in range(r))


@dataclass(frozen=True)
class WeylA1:
    terms: Dict[Monomial, sp.Expr]

    @staticmethod
    def zero() -> "WeylA1":
        return WeylA1({})

    @staticmethod
    def one() -> "WeylA1":
        return WeylA1({(0, 0): sp.Integer(1)})

    @staticmethod
    def scalar(c: sp.Expr) -> "WeylA1":
        c = sp.sympify(c)
        return WeylA1.zero() if c == 0 else WeylA1({(0, 0): c})

    @staticmethod
    def x() -> "WeylA1":
        return WeylA1({(1, 0): sp.Integer(1)})

    @staticmethod
    def d() -> "WeylA1":
        return WeylA1({(0, 1): sp.Integer(1)})

    def clean(self) -> "WeylA1":
        cleaned = {m: sp.simplify(c) for m, c in self.terms.items() if sp.simplify(c) != 0}
        return WeylA1(cleaned)

    def __add__(self, other: "WeylA1") -> "WeylA1":
        out = dict(self.terms)
        for monomial, coeff in other.terms.items():
            out[monomial] = out.get(monomial, 0) + coeff
        return WeylA1(out).clean()

    def __neg__(self) -> "WeylA1":
        return WeylA1({m: -c for m, c in self.terms.items()}).clean()

    def __sub__(self, other: "WeylA1") -> "WeylA1":
        return self + (-other)

    def __mul__(self, other: "WeylA1") -> "WeylA1":
        out: Dict[Monomial, sp.Expr] = {}
        for (i, j), c in self.terms.items():
            for (k, ell), d in other.terms.items():
                # d^j x^k = sum_r binom(j,r) falling(k,r) x^(k-r) d^(j-r)
                for r in range(min(j, k) + 1):
                    monomial = (i + k - r, j + ell - r)
                    coeff = c * d * comb(j, r) * falling(k, r)
                    out[monomial] = out.get(monomial, 0) + coeff
        return WeylA1(out).clean()

    def scale(self, coeff: sp.Expr) -> "WeylA1":
        return WeylA1({m: coeff * c for m, c in self.terms.items()}).clean()

    def fourier(self) -> "WeylA1":
        """Formal Fourier transform x -> -d, d -> x."""
        result = WeylA1.zero()
        minus_d = WeylA1.d().scale(-1)
        x = WeylA1.x()
        for (i, j), coeff in self.terms.items():
            image = WeylA1.one()
            for _ in range(i):
                image = image * minus_d
            for _ in range(j):
                image = image * x
            result = result + image.scale(coeff)
        return result.clean()

    def as_expr(self) -> sp.Expr:
        x, d = sp.symbols("x d", commutative=True)
        return sp.Add(*[coeff * x**i * d**j for (i, j), coeff in self.terms.items()])


def main() -> None:
    a, b, u, v, s = sp.symbols("a b u v s")
    x = WeylA1.x()
    d = WeylA1.d()
    one = WeylA1.one()

    p = (x - WeylA1.scalar(u)) * (x - WeylA1.scalar(v)) * d
    p = p - (x - WeylA1.scalar(v)).scale(a)
    p = p - (x - WeylA1.scalar(u)).scale(b)

    p_hat = p.fourier()
    expected = x * d * d
    expected = expected + (x.scale(u + v) + one.scale(2 + a + b)) * d
    expected = expected + x.scale(u * v) + one.scale(u + v + a * v + b * u)

    assert (p_hat - expected).clean().terms == {}

    b_poly = sp.expand(s * (s - a - b))
    assert sp.simplify(b_poly.subs(s, 0)) == 0
    assert sp.simplify(b_poly.subs(s, a + b)) == 0

    print("oaku_takayama_dmodule_de_rham.py: Weyl A1 witness passed")
    print("Fourier(p) normal form:")
    sp.pprint(p_hat.as_expr())
    print("b-function / indicial polynomial:")
    sp.pprint(b_poly)
    print("roots checked: s=0 and s=a+b")
    print("Full Groebner/resolution/integration pipeline remains a D-module deferred_interface.")


if __name__ == "__main__":
    main()
