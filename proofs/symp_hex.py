import sympy as sp

def main():
    q, s, tau = sp.symbols('q s tau')
    
    hc = q**4 - q**3 + q**2 - q + 1
    h_s_sq = s**2 - (q**2 - q**3)
    
    F = sp.Matrix([
        [tau, s],
        [s, -tau]
    ])
    R = sp.Matrix([
        [q**4, 0],
        [0, -q**2]
    ])
    Rp = sp.Matrix([
        [1, 0],
        [0, -q**2]
    ])
    
    Ri = sp.Matrix([
        [-q, 0],
        [0, q**3]
    ])
    Rpi = sp.Matrix([
        [1, 0],
        [0, q**3]
    ])
    
    LHS_I = R * F * R
    RHS_I = F * Rp * F
    LHS_II = Ri * F * Ri
    RHS_II = F * Rpi * F
    
    print("--- HEXAGON I FACTORIZATION ---")
    for i in range(2):
        for j in range(2):
            diff = sp.expand(LHS_I[i,j] - RHS_I[i,j])
            diff_tau = sp.expand(diff.subs(tau, q**2 - q**3))
            
            C1 = diff_tau.coeff(s**2)
            rem_s2 = sp.expand(diff_tau - C1 * h_s_sq)
            
            coeff_s = rem_s2.coeff(s)
            coeff_const = rem_s2 - coeff_s * s
            
            C2_s, _ = sp.div(coeff_s, hc, q)
            C2_c, _ = sp.div(coeff_const, hc, q)
            C2 = C2_c + C2_s * s
            
            print(f"Cell({i},{j}) -> LHS - RHS = ({sp.simplify(C1)}) * (s^2 - tau) + ({sp.simplify(C2)}) * (hc)")
            
    print("\n--- HEXAGON II FACTORIZATION ---")
    for i in range(2):
        for j in range(2):
            diff = sp.expand(LHS_II[i,j] - RHS_II[i,j])
            diff_tau = sp.expand(diff.subs(tau, q**2 - q**3))
            
            C1 = diff_tau.coeff(s**2)
            rem_s2 = sp.expand(diff_tau - C1 * h_s_sq)
            
            coeff_s = rem_s2.coeff(s)
            coeff_const = rem_s2 - coeff_s * s
            
            C2_s, _ = sp.div(coeff_s, hc, q)
            C2_c, _ = sp.div(coeff_const, hc, q)
            C2 = C2_c + C2_s * s
            
            print(f"Cell({i},{j}) -> LHS - RHS = ({sp.simplify(C1)}) * (s^2 - tau) + ({sp.simplify(C2)}) * (hc)")

if __name__ == "__main__":
    main()
