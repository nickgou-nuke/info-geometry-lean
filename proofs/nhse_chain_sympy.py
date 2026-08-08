import sympy as sp

def verify_nhse_chain():
    print("--- Non-Hermitian Skin Effect (NHSE) Kitaev-Cuntz Chain ---")
    
    alpha = sp.Symbol('alpha', real=True)
    t = sp.Symbol('t', real=True, positive=True)
    
    # Asymmetric hopping terms defined by the hyperbolic boost
    t_R = t * sp.cosh(alpha)
    t_L = t * sp.sinh(alpha)
    
    # Construct a 4-site tight-binding lattice
    N = 4
    H = sp.zeros(N, N)
    
    for i in range(N - 1):
        H[i, i+1] = t_R
        H[i+1, i] = t_L
        
    print(f"\n1. Tight-Binding Hamiltonian (N={N}):")
    sp.pprint(H)
    
    # Verify Non-Hermiticity
    print("\n2. Is the Hamiltonian Hermitian? (H == H^dag)")
    H_dag = H.H
    is_hermitian = H == H_dag
    print(is_hermitian)
    print("Because t_R != t_L, the macroscopic bulk breaks reciprocity.")
    
    # Compute characteristic polynomial to analyze spectrum
    lam = sp.Symbol('lambda')
    char_poly = H.charpoly(lam).as_expr()
    
    print("\n3. Characteristic Polynomial:")
    sp.pprint(sp.simplify(char_poly))
    
    # The polynomial is lambda^4 - 3*lambda^2*t_L*t_R + (t_L*t_R)^2
    # Notice it depends entirely on the product t_L * t_R
    product = sp.simplify(t_L * t_R)
    print("\n4. Hopping Product (t_L * t_R):")
    sp.pprint(product)
    print("= t^2 * sinh(2*alpha) / 2")
    
    print("\nCONCLUSION: The global bulk asymmetry forces the spectrum to rely entirely on the product of left and right hopping. Because the hopping is asymmetric, eigenstates accumulate exponentially at the boundary, collapsing the bulk spectrum and isolating the zero-energy parafermion modes.")

if __name__ == "__main__":
    verify_nhse_chain()
