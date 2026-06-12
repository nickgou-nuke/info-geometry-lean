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
    J = sp.Matrix(
        [
            [0, 0, -1, 0],
            [0, 0, 0, 1],
            [1, 0, 0, 0],
            [0, -1, 0, 0],
        ]
    )
    K = sp.Matrix(
        [
            [0, 0, 0, -1],
            [0, 0, -1, 0],
            [0, 1, 0, 0],
            [1, 0, 0, 0],
        ]
    )

    eye4 = sp.eye(4)
    assert I * I == -eye4
    assert J * J == -eye4
    assert K * K == -eye4
    assert I * J == K
    assert J * I == -K

    x0, x1, x2, x3, y0, y1, y2, y3 = sp.symbols("x0 x1 x2 x3 y0 y1 y2 y3")
    x = sp.Matrix([x0, x1, x2, x3])
    y = sp.Matrix([y0, y1, y2, y3])

    omega_xy = (I * x).dot(y)
    omega_yx = (I * y).dot(x)
    assert sp.simplify(omega_xy + omega_yx) == 0

    fisher = eye4
    assert fisher.T == fisher
    assert sp.simplify((x.T * fisher * x)[0] - sum(c**2 for c in x)) == 0

    sigma_x = sp.Matrix([[0, 1], [1, 0]])
    sigma_y_real = sp.Matrix([[0, -1], [1, 0]])
    assert sigma_x * sigma_x + sigma_y_real * sigma_y_real == sp.zeros(2)

    print("Biquaternion-Kahler finite algebra checks passed.")


if __name__ == "__main__":
    main()
