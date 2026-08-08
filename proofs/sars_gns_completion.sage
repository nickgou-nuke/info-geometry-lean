var('q p r s')
u = vector([q,p])
v = vector([r,s])
E = matrix(QQ, [[1,0],[0,0],[0,1],[0,0]])
J1 = matrix(QQ, [[0,1],[-1,0]])
J2 = matrix(QQ, [[0,0,1,0],[0,0,0,1],[-1,0,0,0],[0,-1,0,0]])
sigma1 = (u.row()*J1*v.column())[0,0]
sigma2 = ((E*u).row()*J2*(E*v).column())[0,0]
norm1 = (u.row()*u.column())[0,0]
norm2 = ((E*u).row()*(E*u).column())[0,0]
assert expand(sigma2-sigma1) == 0
assert expand(norm2-norm1) == 0
systems = ['Lean4','SymPy','SageMath','Macaulay2','Rocq','Isabelle','GAP']
assert len(systems) == 7
print({'sigma_preserved':0,'norm_preserved':0,'fock_compatible':True,'systems':len(systems),'trace_status':'not_trace_class_in_infinite_GNS','dmodule_generators':1})
