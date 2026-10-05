var('m m0 lam hbar c x E')
PR = matrix(QQ, [[1,0],[0,0]])
PL = matrix(QQ, [[0,0],[0,1]])
I2 = identity_matrix(SR,2)
J = matrix(QQ, [[0,1],[1,0]])
M = m*J
diag = matrix(SR, [[M[0,0],0],[0,M[1,1]]])
off = matrix(SR, [[0,M[0,1]],[M[1,0],0]])
assert PR*PL == zero_matrix(QQ,2)
assert PR+PL == I2
assert J*PL*J == PR
assert J*PR*J == PL
assert M == matrix(SR, [[0,m],[m,0]])
assert diag == zero_matrix(SR,2)
assert off == M
local_mass = m0*exp(lam)
compton = hbar/(m*c)
rest_gap_frequency = 2*m*c^2/hbar
characteristic = (M - E*I2).det()
assert expand(characteristic - (E-m)*(E+m)) == 0
spring = m^2 * lam^2 / 2
force = -diff(spring, lam)
entropy_quad = x^2/2
assert simplify(force + m^2*lam) == 0
assert spring.subs(lam=0) == 0
assert entropy_quad.subs(x=0) == 0
print({'projectors_orthogonal': True, 'tomita_swap': True, 'mass_offblock': True, 'characteristic': factor(characteristic), 'local_mass': local_mass, 'compton': compton, 'rest_gap_frequency': rest_gap_frequency, 'hooke_force': force, 'spring_vacuum_zero': True})
