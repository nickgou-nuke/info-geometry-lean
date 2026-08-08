from sympy import symbols, Matrix, simplify
from galgebra.ga import Ga
coords = symbols('x y')
ga = Ga('e', g=[1, 1], coords=coords)
e1, e2 = ga.mv()
A_x, A_y, B_x, B_y, C_x, C_y = symbols('A_x A_y B_x B_y C_x C_y')
BA = (A_x - B_x)*e1 + (A_y - B_y)*e2
BC = (C_x - B_x)*e1 + (C_y - B_y)*e2
bivec = BA ^ BC
print(bivec.obj)
try:
    print(bivec.get_coefs(2))
except Exception as e:
    print("error1:", e)
