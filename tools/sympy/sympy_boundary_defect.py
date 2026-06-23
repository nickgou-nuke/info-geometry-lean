import sympy as sp

def compute_boundary_defects(N_val):
    # Create non-commutative symbols for J and psi
    def J(k):
        return sp.Symbol(f'J_{k}', commutative=False)
    
    def psi(k):
        return sp.Symbol(f'psi_{k}', commutative=False)

    # Definitions
    def G_trunc(N, r):
        return sum(J(k) * psi(r - k) for k in range(-N, N + 1))

    def L_bosonic_trunc(N, m):
        return sum(J(k) * J(m - k) for k in range(-N, N + 1))

    def L_fermionic_trunc(N, m):
        return sum(k * psi(-k) * psi(k + m) for k in range(-N, N + 1))

    def L_trunc(N, m):
        return L_bosonic_trunc(N, m) + L_fermionic_trunc(N, m)

    # Commutators and Anti-commutators
    def comm(A, B):
        return sp.expand(A * B - B * A)

    def anticomm(A, B):
        return sp.expand(A * B + B * A)

    # Evaluate for m=1, r=0
    m = 1
    r = 0
    N = N_val
    
    # We won't try to apply commutation relations yet, just literal expansion 
    # to see what the raw boundary defect looks like algebraically without relations.
    # Wait, the boundary defect is DEFINED as the difference.
    # But if we want to show it vanishes when applying the oscillator relations, we need to apply them.
    print(f"--- SymPy Witness Evidence (N={N}) ---")
    print("SymPy environment ready.")
    
    # Let's define rules for the oscillator algebra
    # [J_k, J_m] = k * delta_{k+m, 0}
    # {psi_k, psi_m} = delta_{k+m, 0}
    # [J_k, psi_m] = 0
    
    # SymPy doesn't easily apply these automatically on large sums without custom rules.
    # We can just print the exact truncated expressions for now.
    
    G0 = G_trunc(N, 0)
    L1 = L_trunc(N, 1)
    
    print(f"G_trunc(N={N}, r=0) = {G0}")
    print(f"L_trunc(N={N}, m=1) = {L1}")

if __name__ == "__main__":
    compute_boundary_defects(1)
