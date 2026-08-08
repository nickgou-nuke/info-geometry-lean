import sympy as sp


K, c, trace_delta, trace_id, neg_log_delta = sp.symbols(
    "K c trace_delta trace_id neg_log_delta", real=True
)

master = sp.exp(K) - 1 - K
shifted = sp.exp(K + c) - 1 - K - c
assert sp.simplify(shifted - (sp.exp(c) * sp.exp(K) - 1 - K - c)) == 0

is_divergence = sp.exp(K) / 1 - sp.log(sp.exp(K)) - 1
assert sp.simplify(is_divergence - master) == 0

derivative_tick = (sp.exp(K + 1) - 1 - (K + 1)) - master
assert sp.simplify(derivative_tick - (sp.exp(K) * (sp.E - 1) - 1)) == 0
assert sp.simplify((sp.exp(0) - 1 - 0)) == 0

evaluated = trace_delta - trace_id + neg_log_delta
assert sp.simplify(evaluated - (trace_delta - trace_id + neg_log_delta)) == 0

print("master_equation.py: exp(K)-1-K identities verified")
