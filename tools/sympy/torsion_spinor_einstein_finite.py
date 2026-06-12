import sympy as sp


def main():
    a = sp.symbols("a", real=True)

    # Fully antisymmetric torsion sample: T^rho_{mu nu} = a * eps_{rho mu nu 3}
    def eps4(i, j, k, l):
        return sp.LeviCivita(i, j, k, l)

    def T(rho, mu, nu):
        return a * eps4(rho, mu, nu, 3)

    def K(lam, mu, nu):
        return sp.Rational(1, 2) * (T(lam, mu, nu) + T(mu, lam, nu) + T(nu, lam, mu))

    # Torsion antisymmetry and contorsion antisymmetry in first two slots for fully antisymmetric sample.
    for rho in range(4):
        for mu in range(4):
            for nu in range(4):
                assert sp.simplify(T(rho, mu, nu) + T(rho, nu, mu)) == 0
                assert sp.simplify(K(lam=rho, mu=mu, nu=nu) + K(mu, rho, nu)) == 0

    def torsion_norm(tensor):
        return sum(tensor(i, j, k) ** 2 for i in range(4) for j in range(4) for k in range(4))

    def torsion_contraction(tensor, mu, nu):
        return sum(tensor(mu, a1, b1) * tensor(nu, a1, b1) for a1 in range(4) for b1 in range(4))

    def torsion_stress(alpha, tensor, mu, nu):
        contraction = torsion_contraction(tensor, mu, nu)
        delta = 1 if mu == nu else 0
        return sp.expand(
            2 * alpha * (contraction - sp.Rational(1, 4) * delta * torsion_norm(tensor))
        )

    def TT(mu, nu):
        return torsion_stress(1, T, mu, nu)

    # Torsion-squared stress tensor symmetry.
    for mu in range(4):
        for nu in range(4):
            assert sp.simplify(TT(mu, nu) - TT(nu, mu)) == 0

    # Spinor-source antisymmetry using a direct antisymmetric sample with free coefficients c_rho.
    c0, c1, c2, c3, kappa, beta = sp.symbols('c0 c1 c2 c3 kappa beta', real=True)
    coeffs = [c0, c1, c2, c3]

    def S(lam, mu, nu):
        return coeffs[lam] * eps4(lam, mu, nu, 3)

    def Tspin(lam, mu, nu):
        return kappa * beta * S(lam, mu, nu)

    for lam in range(4):
        for mu in range(4):
            for nu in range(4):
                assert sp.simplify(Tspin(lam, mu, nu) + Tspin(lam, nu, mu)) == 0

    alpha = sp.symbols('alpha', real=True)
    scale = (kappa * beta) ** 2
    for mu in range(4):
        for nu in range(4):
            assert sp.simplify(
                torsion_contraction(Tspin, mu, nu) - scale * torsion_contraction(S, mu, nu)
            ) == 0
            assert sp.simplify(
                torsion_stress(alpha, Tspin, mu, nu) - torsion_stress(alpha * scale, S, mu, nu)
            ) == 0

    assert sp.simplify(torsion_norm(Tspin) - scale * torsion_norm(S)) == 0

    # Symmetric residual from symmetric Einstein/Bach/stress inputs.
    G01, G02, G03, G12, G13, G23 = sp.symbols('G01 G02 G03 G12 G13 G23', real=True)
    H01, H02, H03, H12, H13, H23 = sp.symbols('H01 H02 H03 H12 H13 H23', real=True)
    P01, P02, P03, P12, P13, P23 = sp.symbols('P01 P02 P03 P12 P13 P23', real=True)
    diagG = sp.symbols('G00 G11 G22 G33', real=True)
    diagH = sp.symbols('H00 H11 H22 H33', real=True)
    diagP = sp.symbols('P00 P11 P22 P33', real=True)
    diagT = sp.symbols('T00 T11 T22 T33', real=True)
    lamC = sp.symbols('lamC', real=True)

    def sym_from_data(diag, off):
        def f(i, j):
            if i == j:
                return diag[i]
            key = tuple(sorted((i, j)))
            return off[key]
        return f

    offG = {(0,1): G01, (0,2): G02, (0,3): G03, (1,2): G12, (1,3): G13, (2,3): G23}
    offH = {(0,1): H01, (0,2): H02, (0,3): H03, (1,2): H12, (1,3): H13, (2,3): H23}
    offP = {(0,1): P01, (0,2): P02, (0,3): P03, (1,2): P12, (1,3): P13, (2,3): P23}
    G = sym_from_data(diagG, offG)
    H = sym_from_data(diagH, offH)
    P = sym_from_data(diagP, offP)

    def delta(i, j):
        return 1 if i == j else 0

    def Residual(mu, nu):
        return sp.expand(G(mu, nu) + lamC * delta(mu, nu) + H(mu, nu) - (P(mu, nu) + TT(mu, nu)))

    for mu in range(4):
        for nu in range(4):
            assert sp.simplify(Residual(mu, nu) - Residual(nu, mu)) == 0
            lhs_minus_rhs = sp.expand(G(mu, nu) + lamC * delta(mu, nu) + H(mu, nu) - (P(mu, nu) + TT(mu, nu)))
            assert sp.simplify(Residual(mu, nu) - lhs_minus_rhs) == 0

    print('Torsion-spinor-Einstein finite checks passed.')


if __name__ == '__main__':
    main()
