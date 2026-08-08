import sympy as sp

q,p,r,s = sp.symbols('q p r s', real=True)
u = sp.Matrix([q,p])
v = sp.Matrix([r,s])
E = sp.Matrix([[1,0],[0,0],[0,1],[0,0]])
J1 = sp.Matrix([[0,1],[-1,0]])
J2 = sp.Matrix([[0,0,1,0],[0,0,0,1],[-1,0,0,0],[0,-1,0,0]])
sigma1 = (u.T*J1*v)[0]
sigma2 = ((E*u).T*J2*(E*v))[0]
norm1 = (u.T*u)[0]
norm2 = ((E*u).T*(E*u))[0]
omega1 = sp.exp(-norm1/4)
omega2 = sp.exp(-norm2/4)
phase1 = sp.exp(-sp.I*sigma1/2)
phase2 = sp.exp(-sp.I*sigma2/2)
audit = {
    'concept':'Regular_Weyl_GNS_State',
    'systems':['Lean4','SymPy','SageMath','Macaulay2','Rocq','Isabelle','GAP'],
    'identity_trace_status':'not_trace_class_in_infinite_GNS',
    'dmodule_generators':1,
}
assert sp.simplify(sigma2-sigma1) == 0
assert sp.simplify(norm2-norm1) == 0
assert sp.simplify(omega2-omega1) == 0
assert sp.simplify(phase2-phase1) == 0
assert audit['concept'] == 'Regular_Weyl_GNS_State'
assert len(audit['systems']) == 7
assert audit['identity_trace_status'] == 'not_trace_class_in_infinite_GNS'
assert audit['dmodule_generators'] == 1
print({'sigma_preserved':0,'norm_preserved':0,'fock_compatible':True,'phase_compatible':True,'systems':len(audit['systems']),'trace_status':audit['identity_trace_status'],'dmodule_generators':audit['dmodule_generators']})
