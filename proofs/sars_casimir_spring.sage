var('m C lam')
C_on = -m^2
k = -C
mass_k = m^2
V_C = -C*lam^2/2
V_m = m^2*lam^2/2
F_C = C*lam
F_m = -m^2*lam
bracket = 2*C
assert simplify(k.subs(C=C_on) - mass_k) == 0
assert simplify(V_C.subs(C=C_on) - V_m) == 0
assert simplify(F_C.subs(C=C_on) - F_m) == 0
assert mass_k.subs(m=0) == 0
assert V_m.subs(lam=0) == 0
assert simplify(F_m + mass_k*lam) == 0
assert bracket == 2*C
for a,b in [(-2,-3),(0,4),(3,5)]:
    assert RDF(V_m.subs({m:a,lam:b})) >= 0
edges = ['labels','identical_to','gives_stiffness','resists','crosses','restores_to']
assert len(edges) == 6
print({'casimir_on_shell':'-m^2','stiffness_difference':0,'potential_difference':0,'force_difference':0,'massless_stiffness':0,'vacuum_potential':0,'dilation_bracket':'2*C','sample_nonnegative':True,'edges':len(edges)})
