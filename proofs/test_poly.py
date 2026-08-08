import sympy as sp
tau, R0, R1 = sp.symbols('tau R0 R1')
s = sp.symbols('s')
F = sp.Matrix([[tau, s], [s, -tau]])
R = sp.Matrix([[R0, 0], [0, R1]])
sigma1 = R
sigma2 = F * R * F
ybe = sigma1 * sigma2 * sigma1 - sigma2 * sigma1 * sigma2
ybe = ybe.subs(s**2, tau).subs(tau**2, 1-tau)
print(sp.expand(ybe))
