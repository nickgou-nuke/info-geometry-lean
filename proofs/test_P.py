import sympy as sp
q, s = sp.symbols('q s')
cyclo = q**4 - q**3 + q**2 - q + 1
tau = q**2 - q**3
P = tau**2 + s**2 - 1
Q1, R1 = sp.div(P, s**2 - tau, s)
Q2, R2 = sp.div(R1, cyclo, q)
print(Q1)
print(Q2)
