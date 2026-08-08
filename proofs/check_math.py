import sympy as sp
q, s = sp.symbols('q s')
cyclo = q**4 - q**3 + q**2 - q + 1
tau = q**2 - q**3

R1 = q**4
Rtau = -q**2
R = sp.Matrix([[R1, 0], [0, Rtau]])
F = sp.Matrix([[tau, s], [s, -tau]])

sigma1 = R
sigma2 = F * R * F
ybe = sigma1 * sigma2 * sigma1 - sigma2 * sigma1 * sigma2

P = sp.expand(ybe[1,0])
Q1, R1_rem = sp.div(P, s**2 - tau, s)
Q2, R2_rem = sp.div(R1_rem, cyclo, q)
diff = sp.expand(P - (Q1 * (s**2 - tau) + Q2 * cyclo))
print("Diff for (1,0):", diff)
