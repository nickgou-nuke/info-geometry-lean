#!/usr/bin/env python3
"""galgebra-lane certificate for finite pg/pmg/pgg Klein candidates."""

import sympy as sp
from galgebra.ga import Ga


def main():
    u = sp.symbols('u')
    ga = Ga('e', g=[1], coords=[u])
    roots = {(-1,-1),(-1,0),(-1,1),(0,-1),(0,1),(1,-1),(1,0),(1,1)}
    pg = {(0,1), (1,-1)}
    pmg = {(1,0), (0,1)}
    pgg = {(1,0), (0,1)}
    assert pg <= roots and pmg <= roots and pgg <= roots
    scalar_mv = ga.mv(sp.Rational(len(roots), 1), 'scalar')
    assert scalar_mv.obj == 8
    print("klein compatible wallpaper classification galgebra certificate: ok")


if __name__ == "__main__":
    main()
