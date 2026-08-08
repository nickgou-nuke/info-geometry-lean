var('x u')
modular = exp(x-u) - 1 - (x-u)
fenchel_gap = exp(x) + exp(u)*u - exp(u) - x*exp(u)
burg = exp(x-u) - (x-u) - 1
assert simplify(fenchel_gap - exp(u)*modular) == 0
assert simplify(burg - modular) == 0
assert simplify(fenchel_gap.subs({x:0,u:0})) == 0
assert simplify(burg.subs({x:0,u:0})) == 0
for a,b in [(-2,0),(0,0),(1,-1),(3,1)]:
    assert RDF(modular.subs({x:a,u:b})) >= 0
edges = [('Metriplectic_Evolution','symplectic_part','WeylSystem'),('Metriplectic_Evolution','metric_part','Wasserstein_Gradient_Flow'),('Wasserstein_Gradient_Flow','minimizes_distortion','Itakura_Saito_Divergence'),('Itakura_Saito_Divergence','generated_by','Legendre_Fenchel_Duality'),('Legendre_Fenchel_Duality','stabilizes_vacuum','Metriplectic_Evolution')]
assert len(edges) == 5
print({'fenchel_factor':0,'burg_modular_difference':0,'sample_nonnegative':True,'vacuum_zero':True,'edges':len(edges)})
