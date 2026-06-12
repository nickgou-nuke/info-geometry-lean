import sympy as sp

def verify_two_band_model():
    print("=== 2-Band Non-Hermitian Brillouin Klein Bottle Model ===")
    kx, ky = sp.symbols('kx ky', real=True)
    alpha, beta, gamma = sp.symbols('alpha beta gamma', real=True)
    
    # Pauli matrices
    s1 = sp.Matrix([[0, 1], [1, 0]])
    s2 = sp.Matrix([[0, -sp.I], [sp.I, 0]])
    
    # Eq. (8): H2(k) = (alpha*cos(kx) - beta)*sigma_1 + (alpha*sin(kx) - I*gamma*cos(ky))*sigma_2
    H2 = (alpha * sp.cos(kx) - beta) * s1 + (alpha * sp.sin(kx) - sp.I * gamma * sp.cos(ky)) * s2
    
    print(f"H2(kx, ky) = \n{H2}")
    
    # Symmetry: U H(kx, ky) U^-1 = H(-kx, ky + pi)
    U = s1
    H2_transformed = sp.simplify(U * H2 * U.inv())
    H2_target = sp.simplify(H2.subs({kx: -kx, ky: ky + sp.pi}))
    
    is_symmetric = H2_transformed == H2_target
    print(f"Glide Reflection Symmetry U*H(kx,ky)*U^-1 == H(-kx,ky+pi): {is_symmetric}")

def verify_three_band_model():
    print("\n=== 3-Band Non-Hermitian Brillouin Klein Bottle Model ===")
    kx, ky = sp.symbols('kx ky', real=True)
    alpha, beta, gamma, delta, epsilon = sp.symbols('alpha beta gamma delta epsilon', real=True)
    
    # F(k) = alpha*cos(kx) + I*beta*sin(kx)*cos(ky) + I*epsilon
    F = alpha * sp.cos(kx) + sp.I * beta * sp.sin(kx) * sp.cos(ky) + sp.I * epsilon
    # G(k) = gamma*cos(2*ky) + I*delta*sin(2*ky) - epsilon
    G = gamma * sp.cos(2*ky) + sp.I * delta * sp.sin(2*ky) - epsilon
    
    # Eq. (12)
    H3 = sp.Matrix([
        [F, -1, 0],
        [-1, 0, -1],
        [0, -1, G]
    ])
    
    print(f"H3(kx, ky) = \n{H3}")
    
    # Symmetry: U H(kx, ky) U^-1 = H(-kx, ky + pi) with U = I
    U = sp.eye(3)
    H3_transformed = sp.simplify(U * H3 * U.inv())
    H3_target = sp.simplify(H3.subs({kx: -kx, ky: ky + sp.pi}))
    
    is_symmetric = H3_transformed == H3_target
    print(f"Glide Reflection Symmetry U*H(kx,ky)*U^-1 == H(-kx,ky+pi) with U=1: {is_symmetric}")

if __name__ == "__main__":
    verify_two_band_model()
    verify_three_band_model()
