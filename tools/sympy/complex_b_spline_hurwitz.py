import sympy as sp

def verify_spline_denominator():
    print("=== Complex B-splines and Hurwitz zeta functions (Forster et al.) ===")
    s, alpha = sp.symbols('s alpha')
    
    # We symbolically represent the Hurwitz zeta function
    def hurwitz_zeta(s, a):
        # SymPy's zeta handles Hurwitz zeta zeta(s, a)
        return sp.zeta(s, a)
    
    # Eq 7: The sum in the denominator
    # sum_{k in Z} 1/(k + alpha)^s = zeta(s, alpha) + e^{-i pi s} zeta(s, 1 - alpha)
    # The RHS is defined as f_+(s, alpha) in the paper:
    f_plus = hurwitz_zeta(s, alpha) + sp.exp(-sp.I * sp.pi * s) * hurwitz_zeta(s, 1 - alpha)
    
    print("f_+(s, alpha) =")
    print(f_plus)
    
    # Let's test a known value. If s = 2, alpha = 1/2
    # zeta(2, 1/2) = pi^2 / 2 * (some factor)
    # e^{-i pi 2} = 1
    # f_+(2, 1/2) = 2 * zeta(2, 1/2) = 2 * (pi^2/2 + pi^2) = pi^2
    val_s2 = f_plus.subs({s: 2, alpha: sp.Rational(1, 2)})
    print(f"\nValue at s=2, alpha=1/2:")
    print(val_s2)

if __name__ == "__main__":
    verify_spline_denominator()
