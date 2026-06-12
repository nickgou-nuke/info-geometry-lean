import sympy as sp


def main():
    I = sp.Matrix(
        [
            [0, -1, 0, 0],
            [1, 0, 0, 0],
            [0, 0, 0, -1],
            [0, 0, 1, 0],
        ]
    )

    x0, x1, x2, x3, y0, y1, y2, y3, z0, z1, z2, z3, a = sp.symbols(
        "x0 x1 x2 x3 y0 y1 y2 y3 z0 z1 z2 z3 a", real=True
    )
    x = sp.Matrix([x0, x1, x2, x3])
    y = sp.Matrix([y0, y1, y2, y3])
    z = sp.Matrix([z0, z1, z2, z3])

    def dot4(u, v):
        return (u.T * v)[0]

    def omega(u, v):
        return dot4(I * u, v)

    formula = -x1 * y0 + x0 * y1 - x3 * y2 + x2 * y3
    assert sp.expand(omega(x, y) - formula) == 0
    assert sp.expand(omega(x, y) + omega(y, x)) == 0
    assert sp.expand(omega(x + z, y) - (omega(x, y) + omega(z, y))) == 0
    assert sp.expand(omega(x, y + z) - (omega(x, y) + omega(x, z))) == 0
    assert sp.expand(omega(a * x, y) - a * omega(x, y)) == 0
    assert sp.expand(omega(x, a * y) - a * omega(x, y)) == 0
    assert sp.expand(omega(x, x)) == 0

    Ix = I * x
    assert sp.expand(omega(x, Ix) - dot4(x, x)) == 0

    print("BiQuaternion-Kahler symplectic finite checks passed.")


if __name__ == "__main__":
    main()
