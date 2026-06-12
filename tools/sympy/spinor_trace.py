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
    
    # Define a generic 4-component spinor
    p0, p1, p2, p3 = sp.symbols('p0 p1 p2 p3', complex=True)
    dp0, dp1, dp2, dp3 = sp.symbols('dp0 dp1 dp2 dp3', complex=True)
    
    Psi = sp.Matrix([p0, p1, p2, p3])
    dPsi = sp.Matrix([dp0, dp1, dp2, dp3])
    Psi_bar = Psi.H * g0
    
    # Test vielbein: e^0 = Psi_bar * gamma^0 * dPsi
    e0 = sp.simplify((Psi_bar * g0 * dPsi)[0])
    print(f"e^0 = {e0}")
    
    e1 = sp.simplify((Psi_bar * g1 * dPsi)[0])
    print(f"e^1 = {e1}")
    
    # Test A_mu: A_0 = Psi_bar * gamma_5 * gamma_0 * Psi
    A0 = sp.simplify((Psi_bar * g5 * g0 * Psi)[0])
    print(f"A_0 = {A0}")
    
    A1 = sp.simplify((Psi_bar * g5 * g1 * Psi)[0])
    print(f"A_1 = {A1}")

if __name__ == "__main__":
    main()
