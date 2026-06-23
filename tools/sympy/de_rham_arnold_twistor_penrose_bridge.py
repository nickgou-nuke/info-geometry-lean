import sympy as sp


def main() -> None:
    t, x, y, z = sp.symbols("t x y z")
    I = sp.I

    pauli = sp.Matrix([
        [t + z, x - I*y],
        [x + I*y, t - z],
    ])

    det = sp.expand(pauli.det())
    target = sp.expand(t**2 - x**2 - y**2 - z**2)

    print("det(pauli) =", det)
    print("target     =", target)
    assert sp.simplify(det - target) == 0

    # A null example: t = 1, x = 1, y = 0, z = 0
    null_det = sp.simplify(pauli.subs({t: 1, x: 1, y: 0, z: 0}).det())
    assert null_det == 0

    print("PASS: determinant carrier matches the Minkowski quadratic form.")


if __name__ == "__main__":
    main()
