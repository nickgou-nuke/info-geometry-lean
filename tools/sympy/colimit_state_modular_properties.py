import sympy as sp
from sympy.physics.quantum.matrixutils import matrix_tensor_product

def verify_modular_tracial_properties():
    print("==================================================")
    print("Tracial and Modular KMS Properties (CPT Colimit)")
    print("==================================================")
    
    # Arbitrary 2x2 matrices for CPT atoms
    a, b, c, d = sp.symbols('a b c d', rational=True)
    x, y, z, w = sp.symbols('x y z w', rational=True)
    
    A = sp.Matrix([[a, b], [c, d]])
    B = sp.Matrix([[x, y], [z, w]])
    
    def normalized_trace(mat):
        return sp.trace(mat) / mat.shape[0]
        
    print("\n--- 1. Type II_1 Tracial Property ---")
    tr_AB = normalized_trace(A * B)
    tr_BA = normalized_trace(B * A)
    
    print("Tr(A B) == Tr(B A):", sp.simplify(tr_AB - tr_BA) == 0)
    
    print("\n--- 2. Type III KMS Modular Property ---")
    # Hamiltonian for the modular flow
    E1, E2 = sp.symbols('E1 E2', rational=True)
    H = sp.Matrix([[E1, 0], [0, E2]])
    beta = sp.Symbol('beta', rational=True)
    
    # Modular automorphism sigma_{i beta}(A) = e^{-beta H} A e^{beta H}
    e_neg_beta_H = sp.Matrix([[sp.exp(-beta*E1), 0], [0, sp.exp(-beta*E2)]])
    e_pos_beta_H = sp.Matrix([[sp.exp(beta*E1), 0], [0, sp.exp(beta*E2)]])
    
    sigma_i_beta_A = e_neg_beta_H * A * e_pos_beta_H
    
    # KMS Gibbs state: omega(X) = Tr(e^{-beta H} X) / Tr(e^{-beta H})
    def gibbs_state(mat):
        return sp.trace(e_neg_beta_H * mat)
        
    omega_AB = gibbs_state(A * B)
    omega_B_sigma_A = gibbs_state(B * sigma_i_beta_A)
    
    print("omega(A B) == omega(B sigma_{i beta}(A)):", sp.simplify(omega_AB - omega_B_sigma_A) == 0)
    
    print("\nVerification Complete.")

if __name__ == "__main__":
    verify_modular_tracial_properties()
