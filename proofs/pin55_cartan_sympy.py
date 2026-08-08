import sympy as sp
from sympy.physics.quantum import TensorProduct

def verify_pin55_projectors():
    print("--- SymPy Symbolic Verification of Pin(5,5) Projectors ---")
    
    # We define J abstractly with the property J**2 = I
    J = sp.Symbol('J', commutative=False)
    I = sp.Symbol('I', commutative=False)
    
    # Define projector operations with symbolic non-commutative symbols
    P_plus = sp.Rational(1, 2) * (I + J)
    P_minus = sp.Rational(1, 2) * (I - J)
    
    # Expansion rules: I*I = I, I*J = J, J*I = J, J*J = I
    def simplify_involutive(expr):
        expr = sp.expand(expr)
        expr = expr.subs(J*J, I)
        expr = expr.subs(I*I, I)
        expr = expr.subs(I*J, J)
        expr = expr.subs(J*I, J)
        return sp.simplify(expr)

    # 1. Idempotency P_+^2 = P_+
    P_plus_sq = simplify_involutive(P_plus * P_plus)
    print(f"P_+^2 = {P_plus_sq}")
    print(f"Is P_+ idempotent? {sp.simplify(P_plus_sq - P_plus) == 0}")

    # 2. Idempotency P_-^2 = P_-
    P_minus_sq = simplify_involutive(P_minus * P_minus)
    print(f"P_-^2 = {P_minus_sq}")
    print(f"Is P_- idempotent? {sp.simplify(P_minus_sq - P_minus) == 0}")

    # 3. Orthogonality P_+ * P_- = 0
    P_ortho = simplify_involutive(P_plus * P_minus)
    print(f"P_+ * P_- = {P_ortho}")
    print(f"Are they orthogonal? {P_ortho == 0}")

if __name__ == '__main__':
    verify_pin55_projectors()
