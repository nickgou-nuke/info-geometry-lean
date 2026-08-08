import sympy as sp

def test_symbolic_ybe():
    print("═══ STRICTLY SYMBOLIC VALIDATION OF FIBONACCI ANYON MATRICES ═══\n")
    
    q, s = sp.symbols('q s')
    
    # Primitive 10th root of unity relation: q^4 - q^3 + q^2 - q + 1 = 0
    cyclo = q**4 - q**3 + q**2 - q + 1
    
    # R-matrix entries in terms of q = exp(i*pi/5)
    R1 = q**4
    Rtau = -q**2
    
    R = sp.Matrix([
        [R1, 0],
        [0, Rtau]
    ])
    
    # Golden ratio tau = (sqrt(5)-1)/2 = 2*cos(2*pi/5) = q^2 - q^3
    tau = q**2 - q**3
    
    # F-matrix
    F = sp.Matrix([
        [tau, s],
        [s, -tau]
    ])
    
    def simplify_fib(M):
        """Simplifies matrix M over Z[q]/(cyclo) and s^2 = tau."""
        M_simp = sp.zeros(2, 2)
        for i in range(2):
            for j in range(2):
                val = sp.expand(M[i, j])
                
                # Replace powers of s up to s^5 iteratively
                while val.has(s**2) or val.has(s**3) or val.has(s**4) or val.has(s**5):
                    val = sp.expand(val.subs({
                        s**5: s*tau**2,
                        s**4: tau**2,
                        s**3: s*tau,
                        s**2: tau
                    }))
                
                # Separate into A + B*s
                val_A = sp.expand(val.subs(s, 0))
                val_B = sp.expand(sp.simplify((val - val_A)/s)) if val != val_A else 0
                
                # Reduce modulo the cyclotomic polynomial
                rem_A = sp.rem(val_A, cyclo, domain='QQ')
                rem_B = sp.rem(val_B, cyclo, domain='QQ') if val_B != 0 else 0
                
                M_simp[i,j] = rem_A + s * rem_B
        return M_simp

    # Verify F^2 = I
    F_sq = simplify_fib(F * F - sp.eye(2))
    print(f"F² - I is zero:          {F_sq == sp.zeros(2, 2)}")
    
    # Hexagon Equation
    R_prime = sp.Matrix([
        [1, 0],
        [0, Rtau]
    ])
    hex_eq = simplify_fib(R * F * R - F * R_prime * F)
    print(f"Right Hexagon is zero:   {hex_eq == sp.zeros(2, 2)}")
    
    # Yang-Baxter Equation
    sigma1 = R
    sigma2 = F * R * F
    ybe = simplify_fib(sigma1 * sigma2 * sigma1 - sigma2 * sigma1 * sigma2)
    print(f"Yang-Baxter is zero:     {ybe == sp.zeros(2, 2)}")

if __name__ == "__main__":
    test_symbolic_ybe()
