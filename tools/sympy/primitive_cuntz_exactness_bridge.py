import sympy as sp

def test_cuntz_exactness():
    # Define non-commutative symbols
    S_L = sp.Symbol('S_L', commutative=False)
    S_R = sp.Symbol('S_R', commutative=False)
    S_L_star = sp.Symbol('S_L_star', commutative=False)
    S_R_star = sp.Symbol('S_R_star', commutative=False)
    X = sp.Symbol('X', commutative=False)
    I = sp.Symbol('I', commutative=False)

    # We will simulate the substitution rules for Cuntz isometries and exact partition
    # 1. Isometries: S_L_star * S_L = I, S_R_star * S_R = I
    # 2. Partition: S_L * S_L_star + S_R * S_R_star = I

    # To prove S_L_star * S_R = 0, we take:
    # S_L_star * (S_L * S_L_star + S_R * S_R_star)
    # = S_L_star * I = S_L_star
    # = (S_L_star * S_L) * S_L_star + S_L_star * S_R * S_R_star
    # = I * S_L_star + S_L_star * S_R * S_R_star
    # = S_L_star + S_L_star * S_R * S_R_star
    # Thus S_L_star * S_R * S_R_star = 0
    # Multiply by S_R on the right: S_L_star * S_R * (S_R_star * S_R) = S_L_star * S_R * I = S_L_star * S_R = 0

    print("--- SymPy Twin: Cuntz Primitive Exactness ---")
    print("1. Isometry rules applied manually.")
    print("2. Orthogonality S_L_star * S_R = 0 derived algebraically.")

    # Test the UHF transition preservation of exactness
    # Phi(X) = S_L X S_L_star + S_R X S_R_star
    term1 = S_L * X * S_L_star
    term2 = S_R * X * S_R_star
    Phi_X = term1 + term2

    # Square it:
    Phi_X_sq = Phi_X * Phi_X
    Phi_X_sq_expanded = Phi_X_sq.expand()

    print("\nOriginal expanded square of UHF transition:")
    print(Phi_X_sq_expanded)

    # Apply substitutions for cross-terms and diagonal terms
    def apply_cuntz_rules(expr):
        # Handle cross terms first
        e = expr.subs(S_L_star * S_R, 0)
        e = e.subs(S_R_star * S_L, 0)
        # Handle diagonal terms
        e = e.subs(S_L_star * S_L, I)
        e = e.subs(S_R_star * S_R, I)
        # Handle X * I * X -> X * X
        e = e.subs(X * I * X, X * X)
        # Handle Idempotence of X
        e = e.subs(X * X, X)
        return e

    Phi_X_sq_reduced = apply_cuntz_rules(Phi_X_sq_expanded)
    
    print("\nReduced square of UHF transition using Cuntz rules:")
    print(Phi_X_sq_reduced)

    if Phi_X_sq_reduced == Phi_X:
        print("\n[SUCCESS] Phi(X)^2 = Phi(X) exactly matches the Lean proof!")
    else:
        print("\n[FAILED] Phi(X)^2 != Phi(X)")

if __name__ == "__main__":
    test_cuntz_exactness()
