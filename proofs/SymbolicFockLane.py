import sympy as sp


def symbolic_lane(m):
    """Return symbolic occupation markers and prime-mode weights."""
    eps = sp.symbols(f"e0:{m}")
    xs = sp.symbols(f"x0:{m}")
    return eps, xs


def impose_idempotent_normal_form(expr, eps):
    """Reduce occupation markers by e_i^2 = e_i."""
    out = sp.expand(expr)
    for e in eps:
        poly = sp.Poly(out, e)
        reduced = 0
        for (power,), coeff in poly.terms():
            reduced += coeff * (e if power else 1)
        out = sp.expand(reduced)
    return sp.expand(out)


def symbolic_word_generator(eps, xs):
    """Product of symbolic occupied/unoccupied local lanes."""
    return sp.expand(sp.prod((1 - e) + e * x for e, x in zip(eps, xs)))


def symbolic_parity_generator(eps):
    """Symbolic fermion parity (-1)^F as product_i (1 - 2 e_i)."""
    return sp.expand(sp.prod(1 - 2 * e for e in eps))


def symbolic_graded_generator(eps, xs):
    """Symbolic supertrace: parity times occupation-weight generator."""
    raw = symbolic_parity_generator(eps) * symbolic_word_generator(eps, xs)
    return impose_idempotent_normal_form(raw, eps)


def boolean_trace_projection(expr, eps):
    """Trace/projection over symbolic Boolean lanes: sum over e_i in {0,1}."""
    out = expr
    for e in eps:
        out = sp.expand(out.subs(e, 0) + out.subs(e, 1))
    return sp.expand(out)


eps, xs = symbolic_lane(3)
e0, e1, e2 = eps
x0, x1, x2 = xs

word_gen = symbolic_word_generator(eps, xs)
parity_gen = symbolic_parity_generator(eps)
graded_gen = symbolic_graded_generator(eps, xs)

# Boolean trace projection sums all symbolic occupation lanes.
ordinary_trace = boolean_trace_projection(word_gen, eps)
graded_trace = boolean_trace_projection(graded_gen, eps)

assert sp.expand(ordinary_trace) == sp.expand((1 + x0) * (1 + x1) * (1 + x2))
assert sp.expand(graded_trace) == sp.expand((1 - x0) * (1 - x1) * (1 - x2))

# Each concrete lane is recovered by substituting e_i in {0,1}.
assert word_gen.subs({e0: 1, e1: 0, e2: 1}) == x0 * x2
assert parity_gen.subs({e0: 1, e1: 0, e2: 1}) == 1
assert parity_gen.subs({e0: 1, e1: 1, e2: 1}) == -1

# The whole CAS lane remains symbolic until the final projection.
s = sp.symbols("s")
primes = [2, 3, 5]
dirichlet_weights = [sp.Pow(p, -s, evaluate=False) for p in primes]
symbolic_dirichlet = symbolic_graded_generator(eps, dirichlet_weights)
finite_mobius_dirichlet = symbolic_dirichlet.subs({e: 1 for e in eps})
finite_mobius_dirichlet = boolean_trace_projection(symbolic_dirichlet, eps)

assert sp.simplify(
    finite_mobius_dirichlet
    - sp.expand(sp.prod(1 - sp.Pow(p, -s, evaluate=False) for p in primes))
) == 0

print("SymbolicFockLane.py: symbolic idempotent occupation lane verified")
