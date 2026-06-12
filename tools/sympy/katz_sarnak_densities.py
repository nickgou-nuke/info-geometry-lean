import sympy as sp

def verify_katz_sarnak_densities():
    print("=== Katz-Sarnak 1-Level Densities of Low-Lying Zeroes ===")
    x = sp.symbols('x', real=True)
    
    # The GUE scaling limits
    w_U = 1
    w_Sp = 1 - sp.sin(2 * sp.pi * x) / (2 * sp.pi * x)
    w_SO_even = 1 + sp.sin(2 * sp.pi * x) / (2 * sp.pi * x)
    # SO(odd) has a Dirac delta at 0, which we can represent symbolically
    delta = sp.Function('delta')
    w_SO_odd = delta(x) + 1 - sp.sin(2 * sp.pi * x) / (2 * sp.pi * x)
    
    print("w^(U)(x) =", w_U)
    print("w^(Sp)(x) =", w_Sp)
    print("w^(SO_even)(x) =", w_SO_even)
    print("w^(SO_odd)(x) =", w_SO_odd)
    
    # Check limit at x -> 0 for Sp and SO_even
    print("\nLimit as x -> 0:")
    print("w^(Sp)(0) =", sp.limit(w_Sp, x, 0))
    print("w^(SO_even)(0) =", sp.limit(w_SO_even, x, 0))
    
    # Note that Sp has repulsion at x=0, SO_even does not.
    
if __name__ == "__main__":
    verify_katz_sarnak_densities()
