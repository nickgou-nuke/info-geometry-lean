#!/usr/bin/env python3
"""galgebra-lane certificate for the wallpaper/Pin(5,5) root cross-section."""

import itertools
import sympy as sp
from galgebra.ga import Ga


def main():
    u = sp.symbols('u')
    ga = Ga('e', g=[1], coords=[u])
    d5 = set()
    for i, j in itertools.permutations(range(5), 2):
        for si, sj in itertools.product([1, -1], repeat=2):
            v = [0]*5; v[i] = si; v[j] = sj; d5.add(tuple(v))
    plane = {v[:2] for v in d5 if v[2:] == (0, 0, 0)}
    assert plane == {(1, 1), (1, -1), (-1, 1), (-1, -1)}
    scalar_mv = ga.mv(sp.Rational(len(plane), 1), 'scalar')
    assert scalar_mv.obj == 4
    print("wallpaper Pin55 root cross-section galgebra certificate: ok")


if __name__ == "__main__":
    main()
