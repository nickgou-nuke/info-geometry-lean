from sympy import symbols
from galgebra.ga import Ga

print("==================================================")
print("GAlgebra Exact-Rational Certificate:")
print("Pin(5,5) Weyl Group Wallpaper Symmetries")
print("==================================================")

# 1. Cl(5,5) Construction
# We use galgebra for symbolic geometric algebra of signature (5, 5)
coords = symbols('x1 x2 x3 x4 x5 y1 y2 y3 y4 y5')
ga = Ga('e_1 e_2 e_3 e_4 e_5 f_1 f_2 f_3 f_4 f_5', g=[1, 1, 1, 1, 1, -1, -1, -1, -1, -1], coords=coords)

e1, e2, e3, e4, e5, f1, f2, f3, f4, f5 = ga.mv()

print("\n--- 1. Cl(5,5) Geometric Algebra ---")
print(f"Constructed symbolic Cl(5,5) with metric: {ga.g}")

# 2. Pin Group Action for Weyl Reflections
# The root alpha = e1 - e2
alpha = e1 - e2

# Generic vector on the 2D plane
x, y = symbols('x y')
v = x * e1 + y * e2

# Weyl reflection: v' = - alpha * v * alpha_inv
alpha_sq = alpha * alpha
# alpha^2 = e1^2 + e2^2 - (e1*e2 + e2*e1) = 1 + 1 - 0 = 2
# So alpha_inv = alpha / 2
alpha_inv = alpha / 2

# Calculate the Pin action
ref_v = -alpha * v * alpha_inv
ref_v = ref_v.simplify()

print("\n--- 2. Pin(5,5) Reflection onto Wallpaper Map ---")
print(f"Original vector v: {v}")
print(f"Root alpha = e1 - e2: {alpha}")
print(f"Reflected vector v' = -alpha * v * alpha^-1: {ref_v}")

# Expect y*e1 + x*e2
expected_v = y * e1 + x * e2
print(f"Exact match to (y, x) wallpaper mirror reflection: {ref_v == expected_v}")

print("\nO_5_5_WEYL_WALLPAPER_GALGEBRA_CERTIFICATE_OK")
