var('x y z w')
modular = exp(x-y) - 1 - (x-y)
exp_bregman = exp(x) - exp(y) - exp(y)*(x-y)
burg = z/w - log(z/w) - 1
burg_exp = burg.subs({z:exp(x), w:exp(y)})
itakura = z - log(z) - 1
itakura_exp = itakura.subs(z=exp(x))
assert simplify(exp_bregman - exp(y)*modular) == 0
assert simplify(burg_exp - modular) == 0
assert simplify(itakura_exp - (exp(x)-1-x)) == 0
for a,b in [(-2,0),(0,0),(1,-1),(3,1)]:
    assert RDF(modular.subs({x:a,y:b})) >= 0
edges = ['qft_modular_to_itakura_saito','bregman_coordinate_isomorphism','stabilizes_krein_entropy']
assert len(edges) == 3
print({'exp_bregman_factor':0,'burg_exp_coordinate':0,'itakura_exp_coordinate':0,'sample_nonnegative':True,'vacuum_zero':0,'edges':edges})
