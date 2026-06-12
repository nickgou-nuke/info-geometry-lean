import sympy as sp

def verify_non_orientable_twisted_ep():
    print("=== Non-orientable Exceptional Points in Twisted Boundary Systems ===")
    kx, ky = sp.symbols('kx ky', real=True)
    alpha, beta, gamma = sp.symbols('alpha beta gamma', real=True)
    
    sx = sp.Matrix([[0, 1], [1, 0]])
    sy = sp.Matrix([[0, -sp.I], [sp.I, 0]])
    
    # Eq. (3), (4)
    dx = sp.cos(kx) + sp.I * alpha
    dy = -sp.sin(kx) * ((1 - gamma)*sp.sin(ky) + gamma*sp.cos(ky)) - sp.Rational(1, 2) + sp.I * beta
    
    H = dx * sx + dy * sy
    print(f"H(k) =\n{H}")
    
    # Eq. (1) Glide symmetry: H(k_x, k_y) = H(-k_x, k_y + \pi)
    H_target = sp.simplify(H.subs({kx: -kx, ky: ky + sp.pi}))
    H_simplified = sp.simplify(H)
    
    is_symmetric = sp.simplify(H_simplified - H_target) == sp.zeros(2)
    print(f"Momentum-space glide symmetry H(kx, ky) == H(-kx, ky+pi): {is_symmetric}")

def verify_ep_pairs_classification():
    print("\n=== Classification of EP pairs (Table I) ===")
    z, z1, z2 = sp.symbols('z z1 z2')
    
    # Case 1: H(z) = [0, z-z1; (z-z2)^*, 0] -> at origin [0, z; z^*, 0]
    H1 = sp.Matrix([[0, z], [sp.conjugate(z), 0]])
    
    # Case 2: H(z) = [0, 1; (z-z1)(z-z2)^*, 0] -> at origin [0, 1; |z|^2, 0]
    H2 = sp.Matrix([[0, 1], [z * sp.conjugate(z), 0]])
    
    # Case 3: H(z) = [0, z-z1; z-z2, 0] -> at origin [0, z; z, 0]
    H3 = sp.Matrix([[0, z], [z, 0]])
    
    # Case 4: H(z) = [0, 1; (z-z1)(z-z2), 0] -> at origin [0, 1; z^2, 0]
    H4 = sp.Matrix([[0, 1], [z**2, 0]])
    
    print("Case 1 Hamiltonian (DP Merging):", H1)
    print("Case 2 Hamiltonian (Defective Merging):", H2)
    print("Case 3 Hamiltonian (VP Merging):", H3)
    print("Case 4 Hamiltonian (Defective Merging):", H4)

if __name__ == "__main__":
    verify_non_orientable_twisted_ep()
    verify_ep_pairs_classification()
