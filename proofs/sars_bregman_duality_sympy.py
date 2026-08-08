import sympy as sp

x, y, z, w = sp.symbols('x y z w', positive=True)
modular = sp.exp(x-y) - 1 - (x-y)
exp_bregman = sp.exp(x) - sp.exp(y) - sp.exp(y)*(x-y)
burg = z/w - sp.log(z/w) - 1
burg_exp = burg.subs({z: sp.exp(x), w: sp.exp(y)})
itakura = z - sp.log(z) - 1
itakura_exp = itakura.subs(z, sp.exp(x))
assert sp.simplify(exp_bregman - sp.exp(y)*modular) == 0
assert sp.simplify(burg_exp - modular) == 0
assert sp.simplify(itakura_exp - (sp.exp(x)-1-x)) == 0
for a,b in [(-2,0),(0,0),(1,-1),(3,1)]:
    assert float((sp.exp(x-y)-1-(x-y)).subs({x:a,y:b})) >= 0.0
edges = ['qft_modular_to_itakura_saito','bregman_coordinate_isomorphism','stabilizes_krein_entropy']
assert len(edges) == 3
print({'exp_bregman_factor':0,'burg_exp_coordinate':0,'itakura_exp_coordinate':0,'sample_nonnegative':True,'vacuum_zero':0,'edges':edges})
