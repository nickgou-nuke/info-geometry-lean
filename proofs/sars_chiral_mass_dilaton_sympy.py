import sympy as sp

m, m0, lam, hbar, c, x, E = sp.symbols('m m0 lam hbar c x E', real=True, nonzero=True)
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
rest_gap_frequency = 2*m*c**2/hbar
characteristic = (M - E*I2).det()
assert sp.expand(characteristic - (E-m)*(E+m)) == 0
spring = m**2 * lam**2 / 2
force = -sp.diff(spring, lam)
entropy_quad = x**2/2
assert sp.simplify(force + m**2*lam) == 0
assert sp.simplify(spring.subs(lam,0)) == 0
assert sp.simplify(entropy_quad.subs(x,0)) == 0
print({'projectors_orthogonal': True, 'tomita_swap': True, 'mass_offblock': True, 'characteristic': sp.factor(characteristic), 'local_mass': str(local_mass), 'compton': str(compton), 'rest_gap_frequency': str(rest_gap_frequency), 'hooke_force': str(force), 'spring_vacuum_zero': True})
