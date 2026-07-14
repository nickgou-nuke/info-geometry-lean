import sympy as sp

z1, z2, z3, z4 = sp.symbols('z1 z2 z3 z4')
z1b, z2b, z3b, z4b = sp.symbols('z1b z2b z3b z4b')

N = (z1 - z3)*(z2 - z4)*(z2b - z3b)*(z1b - z4b) - (z1b - z3b)*(z2b - z4b)*(z2 - z3)*(z1 - z4)

A = (z1*z2b - z1b*z2 + z2*z3b - z2b*z3 + z3*z1b - z3b*z1)

B_bar = -(z1*z1b*(z2b - z3b) + z2*z2b*(z3b - z1b) + z3*z3b*(z1b - z2b))
B = -(z1*z1b*(z2 - z3) + z2*z2b*(z3 - z1) + z3*z3b*(z1 - z2))

C = z1*z1b*(z2*z3b - z2b*z3) + z2*z2b*(z3*z1b - z3b*z1) + z3*z3b*(z1*z2b - z1b*z2)

circle_eq = A * z4 * z4b + B_bar * z4 + B * z4b + C

diff = sp.simplify(N - circle_eq)
print("Difference is:", diff)
