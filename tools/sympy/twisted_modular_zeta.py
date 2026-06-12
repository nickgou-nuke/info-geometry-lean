import sympy as sp

def verify_twisted_zeta_factorization():
    print("=== Zeta Functions of Twisted Modular Curves (Virdol) ===")
    s = sp.symbols('s')
    
    # Symbolically represent the local Euler factors
    q = sp.symbols('q')
    
    # L_q(s) = det(1 - j(rho(Frob_q)) q^{-s})^{-1}
    # For a 2-dimensional representation, the determinant is:
    # 1 - Tr(rho(Frob_q)) q^{-s} + Det(rho(Frob_q)) q^{-2s}
    tr_rho, det_rho = sp.symbols('Tr(\\rho) Det(\\rho)')
    
    L_q_inv = 1 - tr_rho * q**(-s) + det_rho * q**(-2*s)
    print("Inverse local Euler factor L_q(s)^{-1}:")
    print(L_q_inv)
    
    # Twist by a character / representation omega
    # L_q(s, rho \otimes omega) = det(1 - rho(Frob) \otimes omega(Frob) q^{-s})
    tr_omega, det_omega = sp.symbols('Tr(\\omega) Det(\\omega)')
    
    # For a 1-dimensional twist omega (trace=omega, det=omega^2)
    # The trace of tensor product is the product of traces: Tr(rho) * omega
    # The determinant of tensor product is Det(rho) * omega^2
    omega = sp.symbols('omega')
    L_q_twisted_inv = 1 - (tr_rho * omega) * q**(-s) + (det_rho * omega**2) * q**(-2*s)
    
    print("\nInverse twisted local Euler factor L_q(s, rho \otimes omega)^{-1}:")
    print(L_q_twisted_inv)

if __name__ == "__main__":
    verify_twisted_zeta_factorization()
