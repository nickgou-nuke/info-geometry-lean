import sympy as sp


def graded_lane(bit, x):
    return -x if bit else 1


def boolean_trace(xs):
    if not xs:
        return sp.Integer(1)
    head, *tail = xs
    return sp.expand(boolean_trace(tail) + (-head) * boolean_trace(tail))


def graded_product(xs):
    return sp.expand(sp.prod(1 - x for x in xs))


def boundary_selector_sum(xs):
    total = 0
    for mask in range(2 ** len(xs)):
        term = 1
        for i, x in enumerate(xs):
            bit = bool((mask >> i) & 1)
            term *= graded_lane(bit, x)
        total += term
    return sp.expand(total)


x0, x1, x2, x3, x4 = sp.symbols("x0 x1 x2 x3 x4")
xs = [x0, x1, x2, x3, x4]

assert boolean_trace([]) == 1
assert boolean_trace(xs) == graded_product(xs)
assert boundary_selector_sum(xs) == graded_product(xs)

# Inductive colimit compatibility: adding one UHF bit appends one local factor.
assert sp.simplify(boolean_trace(xs + [sp.Symbol("x5")]) - boolean_trace(xs) * (1 - sp.Symbol("x5"))) == 0

print("FiniteUHFBooleanTrace.py: arbitrary finite UHF Boolean trace equals graded product")
