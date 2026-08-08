import sympy as sp

x, z = sp.symbols('x z', positive=True)
modular = sp.exp(x) - 1 - x
itakura = z - sp.log(z) - 1
itakura_exp = itakura.subs(z, sp.exp(x))
assert sp.simplify(itakura_exp - modular) == 0
assert sp.simplify(modular.subs(x, 0)) == 0
for val in [-5,-2,-1,0,1,2,5]:
    assert float(modular.subs(x, val)) >= 0.0

edges = ['exp_coordinate_transform','bregman_dual','stabilizes_modular_flow']
assert len(edges) == 3
assert 'exp_coordinate_transform' in edges
assert 'bregman_dual' in edges
assert 'stabilizes_modular_flow' in edges
print({'identity': 'dIS(exp(x)||1)=exp(x)-1-x', 'difference': sp.simplify(itakura_exp-modular), 'vacuum_zero': modular.subs(x,0), 'sample_nonnegative': True, 'edges': edges})
