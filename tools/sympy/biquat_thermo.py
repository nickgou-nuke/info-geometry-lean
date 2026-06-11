import sympy as sp
from sympy.physics.quantum.dagger import Dagger

def main():
    print("--- Step 4 & 5: Partition Function and Field Equations on Bi-Quaternion Kahler Manifold ---")
    
    # 1. Define Phase Space Coordinates
    # Phi represents the quaternion condensate field, P represents conjugate momentum
    Phi_0, Phi_1, Phi_2, Phi_3 = sp.symbols('Phi_0 Phi_1 Phi_2 Phi_3', real=True)
    P_0, P_1, P_2, P_3 = sp.symbols('P_0 P_1 P_2 P_3', real=True)
    
    # Let m be the mass gap and lambda_c be the self-interaction coupling
    m, lambda_c = sp.symbols('m lambda_c', real=True, positive=True)
    
    # 2. Define the Hamiltonian
    # Kinetic energy term (flat Kahler metric)
    Kinetic = sp.Rational(1, 2) * (P_0**2 + P_1**2 + P_2**2 + P_3**2)
    # Potential energy (mass term + quartic self-interaction)
    Phi_sq = Phi_0**2 + Phi_1**2 + Phi_2**2 + Phi_3**2
    Potential = sp.Rational(1, 2) * m**2 * Phi_sq + sp.Rational(1, 4) * lambda_c * Phi_sq**2
    
    H = Kinetic + Potential
    print(f"Hamiltonian H = {H}")
    
    # 3. Derive Field Equations using Hamilton's Equations
    # dPhi/dt = dH/dP
    dPhi_0_dt = sp.diff(H, P_0)
    dPhi_1_dt = sp.diff(H, P_1)
    # dP/dt = -dH/dPhi
    dP_0_dt = -sp.diff(H, Phi_0)
    dP_1_dt = -sp.diff(H, Phi_1)
    
    print("\nHamilton's Equations of Motion:")
    print(f"d(Phi_0)/dt = {dPhi_0_dt}")
    print(f"d(P_0)/dt   = {dP_0_dt}")
    
    # 4. Construct Partition Function & Massieu Potential
    # In the free field limit (lambda_c = 0), we can compute the partition function exactly
    beta = sp.Symbol('beta', real=True, positive=True)
    H_free = H.subs(lambda_c, 0)
    
    print(f"\nFree Field Hamiltonian H_free = {H_free}")
    # Partition Function Z = \int exp(-beta H) dP dPhi
    # The integrals separate into 8 Gaussian integrals (4 for P, 4 for Phi)
    Z_P = sp.integrate(sp.exp(-beta * P_0**2 / 2), (P_0, -sp.oo, sp.oo))**4
    Z_Phi = sp.integrate(sp.exp(-beta * m**2 * Phi_0**2 / 2), (Phi_0, -sp.oo, sp.oo))**4
    
    Z = Z_P * Z_Phi
    print(f"Partition Function Z(beta, m) = {Z}")
    
    # Massieu Potential Psi = log(Z)
    Psi = sp.log(Z).simplify()
    print(f"Massieu Potential Psi = {Psi}")
    
    # 5. Connect to Thermodynamics (Internal Energy)
    U = -sp.diff(Psi, beta)
    print(f"Internal Energy U = -d(Psi)/d(beta) = {U}")
    print("This matches the expected equipartition theorem result U = 8 * (1/2 beta) = 4/beta.")

if __name__ == "__main__":
    main()
