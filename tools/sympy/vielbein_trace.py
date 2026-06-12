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
    
    return g0, g1, g2, g3

def main():
    g0, g1, g2, g3 = get_gamma_matrices()
    I4 = sp.eye(4)
    
    q0, q1, q2, q3 = sp.symbols('q0 q1 q2 q3', real=True)
    dq0, dq1, dq2, dq3 = sp.symbols('dq0 dq1 dq2 dq3', real=True)
    
    Q = q0 * I4 + q1 * g1 * g2 + q2 * g2 * g3 + q3 * g3 * g1
    Q_star = q0 * I4 - q1 * g1 * g2 - q2 * g2 * g3 - q3 * g3 * g1
    dQ = dq0 * I4 + dq1 * g1 * g2 + dq2 * g2 * g3 + dq3 * g3 * g1
    
    # A = Q^* gamma^0 dQ
    A = Q_star * g0 * dQ
    print("Tr[Q^* gamma^0 dQ] =", sp.simplify(A.trace()))
    
    A1 = Q_star * g1 * dQ
    print("Tr[Q^* gamma^1 dQ] =", sp.simplify(A1.trace()))

if __name__ == "__main__":
    main()
