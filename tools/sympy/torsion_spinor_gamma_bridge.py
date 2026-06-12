import sympy as sp


def main():
    I = sp.I
    gamma0 = sp.diag(1, 1, -1, -1)
    gamma1 = sp.Matrix([[0, 0, 0, 1], [0, 0, 1, 0], [0, -1, 0, 0], [-1, 0, 0, 0]])
    gamma2 = sp.Matrix([[0, 0, 0, -I], [0, 0, I, 0], [0, I, 0, 0], [-I, 0, 0, 0]])
    gamma3 = sp.Matrix([[0, 0, 1, 0], [0, 0, 0, -1], [-1, 0, 0, 0], [0, 1, 0, 0]])
    gamma = [gamma0, gamma1, gamma2, gamma3]

    def sigma(mu, nu):
        return (I / 4) * (gamma[mu] * gamma[nu] - gamma[nu] * gamma[mu])

    for mu in range(4):
        for nu in range(4):
            assert sp.simplify(sigma(mu, nu) + sigma(nu, mu)) == sp.zeros(4)

    a0, a1, a2, a3 = sp.symbols('a0 a1 a2 a3')
    psi = sp.Matrix([a0, a1, a2, a3])

    def expectation(A):
        return (psi.conjugate().T * A * psi)[0]

    def biv(mu, nu):
        return sp.expand(expectation(gamma0 * sigma(mu, nu)))

    for mu in range(4):
        for nu in range(4):
            assert sp.simplify(biv(mu, nu) + biv(nu, mu)) == 0

    kappa, beta = sp.symbols('kappa beta', real=True)

    def torsion_source(lam, mu, nu):
        return sp.expand(kappa * beta * biv(mu, nu))

    for lam in range(4):
        for mu in range(4):
            for nu in range(4):
                assert sp.simplify(torsion_source(lam, mu, nu) + torsion_source(lam, nu, mu)) == 0

    print('Torsion-spinor gamma bridge finite checks passed.')


if __name__ == '__main__':
    main()
