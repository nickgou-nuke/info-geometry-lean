import sympy as sp

m, m0, lam, hbar, c, x = sp.symbols('m m0 lam hbar c x', real=True, nonzero=True)
PR = sp.Matrix([[1,0],[0,0]])
PL = sp.Matrix([[0,0],[0,1]])
I2 = sp.eye(2)
J = sp.Matrix([[0,1],[1,0]])
M = m*J
diag = sp.Matrix([[M[0,0],0],[0,M[1,1]]])
off = sp.Matrix([[0,M[0,1]],[M[1,0],0]])
assert PR*PL == sp.zeros(2)
assert PR+PL == I2
assert J*PL*J == PR
assert J*PR*J == PL
assert M == sp.Matrix([[0,m],[m,0]])
assert diag == sp.zeros(2)
assert off == M
local_mass = m0*sp.exp(lam)
compton = hbar/(m*c)
zitter = 2*m*c**2/hbar
spring = m**2 * lam**2 / 2
force = -sp.diff(spring, lam)
entropy_quad = x**2/2
assert sp.simplify(force + m**2*lam) == 0
assert sp.simplify(spring.subs(lam,0)) == 0
assert sp.simplify(entropy_quad.subs(x,0)) == 0
edges = ['swapped_by','couples_to','generates','breaks_weyl_scale_by','realizes_as','drives_orthogonal_transport']
assert len(edges) == 6
print({'projectors_orthogonal': True, 'tomita_swap': True, 'mass_offblock': True, 'local_mass': str(local_mass), 'compton': str(compton), 'zitter': str(zitter), 'hooke_force': str(force), 'spring_vacuum_zero': True, 'edges': len(edges)})
