import sympy as sp

def verify_sphere_laplacian_eigenvalues():
    print("=== Determinants of Laplacians on S^10 ===")
    k = sp.symbols('k', integer=True, positive=True)
    n = 10
    
    # Eq (132): eta_k = k(k + n - 1)
    eta_k = k * (k + n - 1)
    
    # Eq (134): alpha_k = eta_k + ((n-1)/2)^2 = (k + (n-1)/2)^2
    alpha_k_derived = sp.simplify(eta_k + sp.Rational(n-1, 2)**2)
    alpha_k_expected = (k + sp.Rational(n-1, 2))**2
    
    print(f"alpha_k derived: {alpha_k_derived}")
    print(f"alpha_k expected (Eq 137): {alpha_k_expected}")
    print(f"Match: {sp.simplify(alpha_k_derived - alpha_k_expected) == 0}")
    
    # Eq (133): q_n(k) = (2k + n - 1) / (n - 1)! * \prod_{j=1}^{n-2} (k + j)
    # For n=10, this is q_10(k)
    q_10_derived = (2*k + 9) / sp.factorial(9) * sp.prod([k + j for j in range(1, 9)])
    print(f"\nq_10(k) derived (Eq 138):")
    print(q_10_derived)
    
    # Check for first few k
    for i in range(1, 4):
        print(f"k={i}: alpha_{i} = {alpha_k_expected.subs(k, i)}, q_10({i}) = {q_10_derived.subs(k, i)}")

if __name__ == "__main__":
    verify_sphere_laplacian_eigenvalues()
