import sympy as sp


def main():
    A = sp.Matrix(
        [
            [0, -1, 0, 0],
            [1, 0, 0, 0],
            [0, 0, 0, -1],
            [0, 0, 1, 0],
        ]
    )

    eye4 = sp.eye(4)
    assert A.T == -A
    assert A * A == -eye4

    x0, x1, x2, x3, p0, p1, p2, p3 = sp.symbols("x0 x1 x2 x3 p0 p1 p2 p3", real=True)
    Phi = sp.Matrix([x0, x1, x2, x3])
    P = sp.Matrix([p0, p1, p2, p3])

    def g(u, v):
        return (u.T * v)[0]

    # Skew-symmetry of the Euclidean Kähler generator.
    assert sp.simplify(g(A * Phi, P) + g(Phi, A * P)) == 0

    # Self-orthogonality of a skew-symmetric generator.
    assert sp.simplify(g(A * P, P)) == 0

    # Quadratic radial potential V(Phi) = 1/2 g(Phi, Phi), gradV(Phi) = Phi.
    gradV = Phi
    assert sp.simplify(g(gradV, A * Phi)) == 0

    # Noether charge derivative for dot(Phi)=P, dot(P)=-gradV(Phi).
    charge_deriv = sp.expand(g(A * P, P) + g(A * Phi, -gradV))
    assert sp.simplify(charge_deriv) == 0

    print("BiQuaternion-Kahler Killing finite checks passed.")


if __name__ == "__main__":
    main()
