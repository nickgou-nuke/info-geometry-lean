import sympy as sp
from sympy.physics.matrices import msigma


def get_gamma_matrices():
    I2 = sp.eye(2)
    Z2 = sp.zeros(2)
    s1, s2, s3 = msigma(1), msigma(2), msigma(3)
    
    g0 = sp.Matrix(sp.BlockMatrix([[I2, Z2], [Z2, -I2]]))
    g1 = sp.Matrix(sp.BlockMatrix([[Z2, s1], [-s1, Z2]]))
    g2 = sp.Matrix(sp.BlockMatrix([[Z2, s2], [-s2, Z2]]))
    g3 = sp.Matrix(sp.BlockMatrix([[Z2, s3], [-s3, Z2]]))
    
    g5 = sp.I * g0 * g1 * g2 * g3
    
    return g0, g1, g2, g3, g5


def main():
    g0, g1, g2, g3, g5 = get_gamma_matrices()
    gammas = [g0, g1, g2, g3]
    I4 = sp.eye(4)
    
    q0, q1, q2, q3 = sp.symbols('q0 q1 q2 q3', real=True)
    dq0, dq1, dq2, dq3 = sp.symbols('dq0 dq1 dq2 dq3', real=True)
    
    Q = q0 * I4 + q1 * g1 * g2 + q2 * g2 * g3 + q3 * g3 * g1
    Q_star = q0 * I4 - q1 * g1 * g2 - q2 * g2 * g3 - q3 * g3 * g1
    
    dQ = dq0 * I4 + dq1 * g1 * g2 + dq2 * g2 * g3 + dq3 * g3 * g1
    
    print("Checking A_mu derivative traces: Tr[Q^* gamma_5 gamma_mu dQ]")
    for mu, gamma_mu in enumerate(gammas):
        a_mu = sp.simplify((Q_star * g5 * gamma_mu * dQ).trace())
        assert a_mu == 0, (mu, a_mu)

    print("Checking F_mu_nu commutator traces: Tr[Q^* gamma_5 [gamma_mu, gamma_nu] Q]")
    for mu, gamma_mu in enumerate(gammas):
        for nu, gamma_nu in enumerate(gammas):
            comm = gamma_mu * gamma_nu - gamma_nu * gamma_mu
            f_mu_nu = sp.simplify((Q_star * g5 * comm * Q).trace())
            assert f_mu_nu == 0, (mu, nu, f_mu_nu)

    print("Quaternionic electromagnetism finite trace obstruction checks passed.")

if __name__ == "__main__":
    main()
