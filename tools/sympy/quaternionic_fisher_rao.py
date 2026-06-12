import sympy as sp

def main():
    print("--- Fisher-Rao Metric on Quaternionic Statistical Manifold ---")
    q0, q1, q2, q3 = sp.symbols('q0 q1 q2 q3', real=True)
    
    # Example thermodynamic potential (log-partition function)
    # For a free quaternion field, Psi is typically quadratic
    Psi = (q0**2 + q1**2 + q2**2 + q3**2) / 2
    
    # Coordinates
    coords = [q0, q1, q2, q3]
    
    # Hessian defines the metric g_ij = d_i d_j Psi
    g = sp.zeros(4, 4)
    for i in range(4):
        for j in range(4):
            g[i, j] = sp.diff(sp.diff(Psi, coords[i]), coords[j])
            
    print("Potential Psi =", Psi)
    print("Metric g_ij (Hessian):")
    sp.pprint(g)
    
    # Verify symmetry
    print("Is metric symmetric?", g == g.T)
    
    # Verify positive definiteness for this example
    eigenvals = list(g.eigenvals().keys())
    print("Eigenvalues of g:", eigenvals)
    print("Is metric positive definite?", all(ev > 0 for ev in eigenvals))

if __name__ == "__main__":
    main()
