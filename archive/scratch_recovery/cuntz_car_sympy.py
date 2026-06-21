import sympy as sp
from sympy.physics.quantum.dagger import Dagger
from sympy.physics.quantum.operator import Operator

# Define Cuntz algebra generators
s1 = Operator('s1')
s2 = Operator('s2')
I = sp.Integer(1)

def apply_cuntz_relations(expr):
    """Recursively apply Cuntz relations: s_i^* s_j = delta_ij, s_1 s_1^* + s_2 s_2^* = 1."""
    expr = expr.expand()
    # Substitute adjoint relations
    expr = expr.subs(Dagger(s1)*s1, I)
    expr = expr.subs(Dagger(s2)*s2, I)
    expr = expr.subs(Dagger(s1)*s2, 0)
    expr = expr.subs(Dagger(s2)*s1, 0)
    # The sum relation s1*s1^* + s2*s2^* = 1 is harder to apply algebraically directly in sympy 
    # as a rewrite rule, but we can do our best.
    return expr

# Definition 1.4: zeta map
def zeta(x):
    return s1 * x * Dagger(s1) - s2 * x * Dagger(s2)

# Recursive Fermion System (RFS) (1.3)
a1 = s1 * Dagger(s2)

def a(n):
    if n == 1:
        return a1
    return zeta(a(n-1)).expand()

# Test CAR relation for n=1, m=1: a1 a1^* + a1^* a1 = I
# a1 a1^* = s1 s2^* s2 s1^* = s1 s1^*
# a1^* a1 = s2 s1^* s1 s2^* = s2 s2^*
# Sum = s1 s1^* + s2 s2^* = I
anti_comm_11 = apply_cuntz_relations(a1 * Dagger(a1) + Dagger(a1) * a1)
print(f"a1 a1^* + a1^* a1 = {anti_comm_11} (should be s1*s1^* + s2*s2^* = 1)")

anti_comm_12 = apply_cuntz_relations(a(1) * Dagger(a(2)) + Dagger(a(2)) * a(1))
print(f"a1 a2^* + a2^* a1 = {anti_comm_12} (should be 0)")
