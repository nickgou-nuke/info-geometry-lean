import sympy as sp

def run_witness_evidence():
    print("=== SymPy Witness Evidence for Concrete Finite Truncations ===")
    
    # Concrete carrier End(R) mapped to scalars in SymPy
    A = sp.Symbol('A', commutative=False)
    B = sp.Symbol('B', commutative=False)
    
    # Nontrivial witness family:
    # J_n = A if n = 0 else 0
    # psi_n = B if n = 1 else 0
    def J(n):
        return A if n == 0 else 0
        
    def psi(n):
        return B if n == 1 else 0
        
    def G_trunc(N, r):
        return sum(J(k) * psi(r - k) for k in range(-N, N + 1))
        
    def L_bosonic_trunc(N, m):
        return sum(J(k) * J(m - k) for k in range(-N, N + 1))
        
    def L_fermionic_trunc(N, m):
        return sum(k * psi(-k) * psi(k + m) for k in range(-N, N + 1))
        
    def L_trunc(N, m):
        return L_bosonic_trunc(N, m) + L_fermionic_trunc(N, m)
        
    # Test for N=1, m=0, r=0
    N = 1
    m = 0
    r = 0
    
    print("\n--- 1. Testing boundaryDefect_LG for (m=0, r=0) ---")
    G_0 = G_trunc(N, 0)
    L_0 = L_trunc(N, 0)
    
    print(f"G_trunc(N={N}, r=0) = {G_0}")
    print(f"L_trunc(N={N}, m=0) = {L_0}")
    
    comm = sp.expand(L_0 * G_0 - G_0 * L_0)
    coeff = m/2 - r
    target = coeff * G_trunc(N, m+r)
    defect = sp.expand(comm - target)
    
    print(f"[L_0, G_0] = {comm}")
    print(f"Target ((0/2 - 0)*G_0) = {target}")
    print(f"boundaryDefect_LG = {defect}")
    assert defect == 0, "Defect should be exactly zero!"
    
    print("\n--- 2. Testing boundaryDefect_GG for (r=0, s=1) ---")
    r = 0
    s = 1
    
    G_0 = G_trunc(N, r)
    G_1 = G_trunc(N, s)
    L_1 = L_trunc(N, r+s)
    
    print(f"G_trunc(N={N}, r=0) = {G_0}")
    print(f"G_trunc(N={N}, s=1) = {G_1}")
    print(f"L_trunc(N={N}, m=1) = {L_1}")
    
    anticomm = sp.expand(G_0 * G_1 + G_1 * G_0)
    target_GG = sp.expand(2 * L_1) # Central term is 0 for this witness
    defect_GG = sp.expand(anticomm - target_GG)
    
    print(f"{{G_0, G_1}} = {anticomm}")
    print(f"Target (2*L_1) = {target_GG}")
    print(f"boundaryDefect_GG = {defect_GG}")
    assert defect_GG == 0, "Defect should be exactly zero!"

if __name__ == "__main__":
    run_witness_evidence()
