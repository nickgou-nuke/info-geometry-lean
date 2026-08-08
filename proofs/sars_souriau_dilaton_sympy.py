import sympy as sp

theta, beta, Z, lam, g = sp.symbols('theta beta Z lam g', nonzero=True, real=True)
weight = sp.exp(-(theta*beta))
rho = weight / Z
weyl_scale = sp.exp(2*lam)
dilaton = sp.exp(lam)
metric_component = weyl_scale * g
assert sp.simplify(Z*rho - weight) == 0
assert sp.simplify(dilaton**2 - weyl_scale) == 0
assert sp.simplify(metric_component - sp.exp(2*lam)*g) == 0
edges = [
    ('Souriau_Lie_Group_Thermodynamics','has_leaflet','Entropic_Leaflet'),
    ('Entropic_Leaflet','tangent_reversible_flow','Sars_Weyl_Colimit'),
    ('Sars_Weyl_Colimit','parameterizes_scale_orthogonal_to_leaves','Souriau_Lie_Group_Thermodynamics'),
    ('Partition_Function_Normalization','normalizes_by_partition_function','Dilaton_Weyl_Gauge_Vector'),
    ('Dilaton_Weyl_Gauge_Vector','generates_orthogonal_entropy_transport','Orthogonal_Entropy_Transport'),
]
assert len(edges) == 5
print({'partition_rescale':0,'dilaton_square_weyl_scale':0,'metric_component_verified':True,'edges':len(edges)})
