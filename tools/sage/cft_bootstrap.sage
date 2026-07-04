tau = SR.var('tau')

def S(z):
    return -1 / z

def T(z):
    return z + 1

def ST(z):
    return S(T(z))

print("=== Continuous Modular Invariants ===")
print("S(tau) =", S(tau))
print("T(tau) =", T(tau))
print()

print("=== Nested Fractional Domain Expansion of (S o T)^3 (tau) ===")
step1 = ST(tau)
print("(S o T)^1(tau) =", step1)

step2 = ST(step1)
print("(S o T)^2(tau) =", step2)

step3 = ST(step2)
print("(S o T)^3(tau) =", step3)
print()

print("=== Explicit Mathematical Expansion ===")
print("Step 2 unsimplified:", step2)
print("Step 2 simplified (rational):", step2.simplify_rational())

print("Step 3 unsimplified:", step3)
print("Step 3 simplified (rational):", step3.simplify_rational())

final_result = step3.full_simplify()
print("Final full_simplify() result:", final_result)
print()

print("=== Algorithmic Proof of (ST)^3 = I ===")
is_identity = bool(final_result == tau)
if is_identity:
    print("Success: (ST)^3(tau) perfectly identically evaluates exactly to tau.")
    print("The strict (ST)^3 = I constraint is established natively.")
else:
    print("Failure: Evaluated to", final_result, "instead of tau")
    raise ValueError("Constraint (ST)^3 = I failed to establish.")
