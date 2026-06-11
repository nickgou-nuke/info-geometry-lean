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
    I4 = sp.eye(4)
    
    q0, q1, q2, q3 = sp.symbols('q0 q1 q2 q3', real=True)
    dq0, dq1, dq2, dq3 = sp.symbols('dq0 dq1 dq2 dq3', real=True)
    
    Q = q0 * I4 + q1 * g1 * g2 + q2 * g2 * g3 + q3 * g3 * g1
    Q_star = q0 * I4 - q1 * g1 * g2 - q2 * g2 * g3 - q3 * g3 * g1
    
    dQ = dq0 * I4 + dq1 * g1 * g2 + dq2 * g2 * g3 + dq3 * g3 * g1
    
    print("Test: A_mu with derivative: Tr[Q^* gamma_5 gamma_mu dQ]")
    A0 = sp.simplify((Q_star * g5 * g0 * dQ).trace())
    A1 = sp.simplify((Q_star * g5 * g1 * dQ).trace())
    print(f"A_0_deriv = {A0}")
    print(f"A_1_deriv = {A1}")
    
    print("\nTest: Electromagnetic tensor F_mu_nu: Tr[Q^* gamma_5 [gamma_mu, gamma_nu] Q]")
    comm01 = g0 * g1 - g1 * g0
    comm12 = g1 * g2 - g2 * g1
    
    F01 = sp.simplify((Q_star * g5 * comm01 * Q).trace())
    F12 = sp.simplify((Q_star * g5 * comm12 * Q).trace())
    print(f"F_01 = {F01}")
    print(f"F_12 = {F12}")

if __name__ == "__main__":
    main()
