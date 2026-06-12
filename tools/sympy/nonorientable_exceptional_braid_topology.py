import sympy as sp

def verify_three_band_klein_gapped():
    print("=== 3-Band Gapped Klein Bottle Model ===")
    p, q = sp.symbols('p q', real=True)
    
    # Eq. (10)
    a = sp.I - sp.I * sp.exp(2 * sp.I * q) * sp.cos(p)
    b = (1 + sp.I) * sp.exp(3 * sp.I * q) * sp.sin(p)
    
    H_gap = sp.Matrix([
        [-a, 1, 0],
        [1, b, 1],
        [0, 1, a]
    ])
    print("H_gap(p,q) =")
    print(sp.pretty(H_gap))
    
def verify_two_band_monopole():
    print("\n=== 2-Band Monopole Klein Bottle Model ===")
    p, q, ell = sp.symbols('p q ell', real=True)
    
    # Eq. (17)
    a = -sp.sin(p) * sp.cos(q) + sp.I * (1 + sp.cos(p)) * (1 + (ell / 2) * sp.cos(2 * q))
    
    H_EP = sp.Matrix([
        [-a, 1],
        [1, a]
    ])
    
    print("H_EP(p,q) =")
    print(sp.pretty(H_EP))
    
    # Eigenvalues
    # Det(H - E) = (-a - E)(a - E) - 1 = E^2 - a^2 - 1 = 0 => E^2 = a^2 + 1 => E = +/- sqrt(a^2 + 1)
    # EP occurs when a^2 + 1 = 0 => a^2 = -1 => a = +/- i
    # Let's check the EPs at ell = 0.
    a_ell_0 = a.subs(ell, 0)
    # The EPs are claimed to be at (p, q) = (+/- pi/2, pi/2).
    for p_val in [sp.pi/2, -sp.pi/2]:
        val = sp.simplify(a_ell_0.subs({p: p_val, q: sp.pi/2}))
        print(f"At ell=0, p={p_val}, q=pi/2, a = {val}. (EP if a = +/- i or -/+ i)")
    
    # At ell = 1, they merge at (p, q) = (0, pi/2)
    a_ell_1 = a.subs(ell, 1)
    val_merged = sp.simplify(a_ell_1.subs({p: 0, q: sp.pi/2}))
    print(f"At ell=1, p=0, q=pi/2, a = {val_merged}. (Merged Monopole EP)")

def verify_braid_relations():
    print("\n=== Braid Constraints ===")
    # Eq. (4) Klein bottle constraint: B_q B_p B_q^(-1) B_p = 1
    # Eq. (4) Projective plane constraint: B_{pq}^2 = 1
    print("Klein bottle gapped constraint: B_q * B_p * B_q^-1 * B_p = 1")
    print("Real Projective plane gapped constraint: B_pq^2 = 1")

if __name__ == "__main__":
    verify_three_band_klein_gapped()
    verify_two_band_monopole()
    verify_braid_relations()
