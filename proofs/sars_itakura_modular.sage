var('x z')
modular = exp(x) - 1 - x
itakura = z - log(z) - 1
itakura_exp = itakura.subs(z=exp(x))
assert simplify(itakura_exp - modular) == 0
assert modular.subs(x=0) == 0
for val in [-5,-2,-1,0,1,2,5]:
    assert RDF(modular.subs(x=val)) >= 0
edges = ['exp_coordinate_transform','bregman_dual','stabilizes_modular_flow']
assert len(edges) == 3
print({'identity':'dIS(exp(x)||1)=exp(x)-1-x','difference':simplify(itakura_exp-modular),'vacuum_zero':modular.subs(x=0),'sample_nonnegative':True,'edges':edges})
