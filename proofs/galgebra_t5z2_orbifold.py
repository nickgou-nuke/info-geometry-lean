import sympy as sp
from galgebra.ga import Ga
from galgebra.printer import Format

Format()

# Coordinates for T^5
coords = sp.symbols('x y z w v', real=True)

# 5D Geometric Algebra
t5_ga = Ga('e', g=[1, 1, 1, 1, 1], coords=coords)

# Jump functions: f_g(x) representing the Z_2 symmetry across the orbifold planes
# We can define a periodic jump function using a Fourier series or piecewise
def jump_func(coord):
    # A simple periodic jump function (square wave) representing the Z_2 jump
    # For a domain [-pi, pi], it's sign(coord)
    return sp.sign(sp.sin(coord))

f_g_x = jump_func(coords[0])
f_g_y = jump_func(coords[1])
f_g_z = jump_func(coords[2])
f_g_w = jump_func(coords[3])
f_g_v = jump_func(coords[4])

# Total jump function on the manifold
total_jump = f_g_x * f_g_y * f_g_z * f_g_w * f_g_v

print("Coordinates:", coords)
print("Total Jump Function defined:")
print(total_jump)

# Derivative of the jump function gives Dirac delta
def delta_func(coord):
    # SymPy's DiracDelta
    return sp.DiracDelta(coord)

# Output some algebraic properties
e_x, e_y, e_z, e_w, e_v = t5_ga.mv()

# A generic vector field on the orbifold
A = sum([coords[i]*t5_ga.mv()[i] for i in range(5)])
print("Vector field A:", A)
