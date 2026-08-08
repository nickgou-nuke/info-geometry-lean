import sympy as sp
q, s = sp.symbols('q s')
cyclo = q**4 - q**3 + q**2 - q + 1
tau = q**2 - q**3

R1 = q**4
Rtau = -q**2
R = sp.Matrix([[R1, 0], [0, Rtau]])
R_prime = sp.Matrix([[1, 0], [0, Rtau]])
F = sp.Matrix([[tau, s], [s, -tau]])

hex_eq = R * F * R - F * R_prime * F

print("Hexagon components:")
for i in range(2):
    for j in range(2):
        P = sp.expand(hex_eq[i,j])
        Q1, R1_rem = sp.div(P, s**2 - tau, s)
        Q2, R2_rem = sp.div(R1_rem, cyclo, q)
        print(f"({i},{j}):")
        print(f"  Q_s = {Q1}")
        print(f"  Q_q = {Q2}")
        print(f"  Remainder = {R2_rem}")
