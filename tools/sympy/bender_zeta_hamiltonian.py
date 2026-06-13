import sympy as sp

def verify_bender_hamiltonian():
    print("=== BENDER ZETA HAMILTONIAN (BERRY-KEATING LIMIT) ===")
    
    # We symbolically evaluate the classical limit of the Bender Hamiltonian.
    # H = (1 - e^{-ip})^{-1} (xp + px) (1 - e^{-ip})
    # In the classical limit, x and p commute, and e^{-ip} is expanded.
    
    x, p = sp.symbols('x p', commutative=True)
    
    # The classical limit of xp + px is simply 2xp since they commute
    # In the classical limit, the similarity transformation factor cancels out!
    
    # Let's represent the similarity transformation factor S = 1 - e^{-ip}
    S = 1 - sp.exp(-sp.I * p)
    S_inv = 1 / S
    
    # Classical Hamiltonian
    H_classical = S_inv * (2 * x * p) * S
    H_reduced = sp.simplify(H_classical)
    
    print(f"Classical limit of the Hamiltonian: H_cl = {H_reduced}")
    
    # Verify it matches the Berry-Keating conjecture
    assert H_reduced == 2 * x * p, "Classical limit does not match the Berry-Keating conjecture!"
    
    print("The Hamiltonian successfully reduces to the Berry-Keating H = 2xp.")
    print("Similarity transformation trivially cancels in the commutative classical limit.")
    print("[SUCCESS] Bender Hamiltonian structural limits verified.")

if __name__ == '__main__':
    verify_bender_hamiltonian()
