import sympy as sp
q, s = sp.symbols('q s')
cyclo = q**4 - q**3 + q**2 - q + 1
R1 = q**4
Rtau = -q**2
R = sp.Matrix([[R1, 0], [0, Rtau]])
tau = q**2 - q**3
F = sp.Matrix([[tau, s], [s, -tau]])
sigma1 = R
sigma2 = F * R * F
ybe = sigma1 * sigma2 * sigma1 - sigma2 * sigma1 * sigma2

ybe_simp = sp.zeros(2, 2)
for i in range(2):
    for j in range(2):
        val = sp.expand(ybe[i, j])
        val = val.subs(s**2, tau)
        val_A = val.subs(s, 0)
        val_B = sp.simplify((val - val_A)/s) if val != val_A else 0
        rem_A = sp.rem(val_A, cyclo, domain='QQ')
        rem_B = sp.rem(val_B, cyclo, domain='QQ') if val_B != 0 else 0
        ybe_simp[i,j] = rem_A + s * rem_B

sp.pprint(ybe_simp)
