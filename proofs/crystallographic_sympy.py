import sympy as sp

def main():
    theta = sp.Symbol('theta', real=True)
    n = sp.Symbol('n', integer=True, positive=True)
    
    # Define a 2D Rotation Matrix
    R = sp.Matrix([
        [sp.cos(theta), -sp.sin(theta)],
        [sp.sin(theta), sp.cos(theta)]
    ])
    
    trace = R.trace()
    print("--- General 2D Rotation Matrix Trace ---")
    print(f"Trace(R) = {trace}")
    print("\n--- The Crystallographic Restriction vs The Pentagon ---")
    print("Classical physics requires Trace(R) to be an integer.")
    print("Let's substitute theta = 2*pi / n for various symmetries:\n")

    for val in [2, 3, 4, 6, 5]:
        val_trace = trace.subs(theta, 2 * sp.pi / val)
        val_trace_simp = sp.simplify(val_trace)
        is_int = val_trace_simp.is_integer
        
        print(f"n = {val} (Angle = 360/{val} degrees):")
        print(f"  Exact Trace = {val_trace_simp}")
        
        if is_int:
            print(f"  Result: Classical, Commutative (Integer: {is_int})")
        else:
            # We know n=5 trace is exactly the Golden Ratio minus 1
            min_poly = sp.minpoly(val_trace_simp)
            phi = sp.GoldenRatio
            
            print(f"  Result: QUANTUM, Non-Commutative (Integer: {is_int})")
            print(f"  Minimal Polynomial: {min_poly}")
            print(f"  Numeric Approximation: {val_trace_simp.evalf(5)}")
            
            # Show relation to Golden Ratio
            phi_rel = sp.simplify(val_trace_simp - (phi - 1))
            if phi_rel == 0:
                print(f"  TOPOLOGICAL MATCH: The trace is exactly phi - 1 (The Golden Ratio minus 1)!")
        
        print("-" * 40)

if __name__ == "__main__":
    main()
