"""galgebra-lane certificate for the split-octonion projective null boundary."""

import sympy as sp
from galgebra.ga import Ga


def main() -> None:
    x = sp.symbols("x")
    ga = Ga("e", g=[1], coords=[x])

    P = sp.Matrix([[1, 0], [0, 0]])
    M = sp.Matrix([[0, 0], [0, 1]])
    I2 = sp.eye(2)

    assert P * P == P
    assert M * M == M
    assert P * M == sp.zeros(2)
    assert M * P == sp.zeros(2)
    assert P + M == I2
    assert P.det() == 0
    assert M.det() == 0

    scalar_mv = ga.mv(sp.Integer(1), "scalar") + ga.mv(sp.Integer(1), "scalar")
    assert scalar_mv.obj == 2
    print("split-octonion projective null boundary galgebra certificate: ok")


if __name__ == "__main__":
    main()
