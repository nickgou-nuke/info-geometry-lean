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

print("YBE components:")
for i in range(2):
    for j in range(2):
        P = sp.expand(ybe[i,j])
        # We want to find A, B such that P = A * cyclo + B * (s**2 - tau)
        # B is simply the coefficient of s**2, s**4 etc.
        # Actually since P has s up to s**5, we can do polynomial division.
        # Let's replace s**2 with tau first
        rem1, B_poly = sp.div(P, s**2 - tau, domain='QQ')
        # wait, div by s**2 - tau treats s as variable
        B_poly = sp.simplify((P - rem1)/(s**2 - tau)) # wait, div returns q, r such that P = q*den + r
        Q1, R1_rem = sp.div(P, s**2 - tau, s)
        Q2, R2_rem = sp.div(R1_rem, cyclo, q)
        
        print(f"({i},{j}):")
        print(f"  Q_s = {Q1}")
        print(f"  Q_q = {Q2}")
        print(f"  Remainder = {R2_rem}")
