import sympy as sp

def verify_contragredient():
    print("=== SymPy Contragredient Legendre-Fenchel Invariance ===")
    a, b, c, d = sp.symbols('a b c d', real=True)
    M = sp.Matrix([[a, b], [c, d]])
    
    theta1, theta2 = sp.symbols('theta1 theta2', real=True)
    eta1, eta2 = sp.symbols('eta1 eta2', real=True)
    
    theta = sp.Matrix([theta1, theta2])
    eta = sp.Matrix([eta1, eta2])
    
    # Primal mapping M * theta
    theta_prime = M * theta
    
    # Contragredient mapping: (M^-1)^T = adj(M)^T / det(M)
    # We enforce the projective gauge det(M) = 1, so (M^-1)^T = [[d, -c], [-b, a]]
    M_inv_T = sp.Matrix([[d, -c], [-b, a]])
    eta_prime = M_inv_T * eta
    
    # Bilinear pairing: <eta, theta>
    inner_orig = (eta.T * theta)[0]
    inner_prime = sp.expand((eta_prime.T * theta_prime)[0])
    
    # Apply the SL(2,C) boundary condition a*d - b*c = 1
    collected = sp.collect(inner_prime, [eta1*theta1, eta2*theta2])
    inner_prime_simp = sp.simplify(collected.subs(a*d - b*c, 1))
    
    assert sp.simplify(inner_orig - inner_prime_simp) == 0, "Contact structure broken!"
    print("[OK] Contact structure <eta, theta> strictly invariant under SL(2,C) contragredient map.")
    
    print("=== SymPy Parabolic Clock ===")
    t = sp.Symbol('t', real=True)
    K = sp.Matrix([[0, 1], [0, 0]])
    assert K**2 == sp.zeros(2)
    exp_K = sp.eye(2) + t * K
    print("Parabolic limit matrix exp(tK):\n", exp_K)
    print("SYMPY_PARABOLIC_CONTRAGREDIENT_OK")

if __name__ == "__main__":
    verify_contragredient()
