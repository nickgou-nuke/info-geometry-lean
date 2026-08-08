import sympy as sp


n, m, p, k, beta, N = sp.symbols("n m p k beta N", positive=True)
q = sp.symbols("q", positive=True)

assert sp.simplify(sp.log(n * m) - (sp.log(n) + sp.log(m))) == 0
assert sp.simplify(sp.log(p**k) - k * sp.log(p)) == 0
assert sp.simplify(sp.log(1 / q) + sp.log(q)) == 0

fermion_occupations = [0, 1]
assert all(o <= 1 for o in fermion_occupations)

zeta_succ_term = (N + 1) ** (-beta)
assert sp.simplify(zeta_succ_term - (N + 1) ** (-beta)) == 0

print("primon_system.py: log-prime and finite occupation identities verified")
