import sympy as sp
from galgebra.ga import Ga
from galgebra.printer import Format, xpdf

Format()

# Define Algebra of Physical Space (APS) which maps to SL(2,C)
# 3D Euclidean space
aps = Ga('e_1 e_2 e_3', g=[1, 1, 1], coords=sp.symbols('x y z'))
e1, e2, e3 = aps.mv()

# Basis for even subalgebra (spinors)
# Spinors in APS are even multivectors: scalar + bivectors
# 1, I1=e2*e3, I2=e3*e1, I3=e1*e2
I1 = e2 * e3
I2 = e3 * e1
I3 = e1 * e2

print("--- 2x2 SL(2,C) Spinors in Geometric Algebra ---")
print("Basis for Spinors (Even Multivectors):")
print(f"1: {aps.mv(1)}")
print(f"I1: {I1}")
print(f"I2: {I2}")
print(f"I3: {I3}")

# Define a general spinor (SL(2,C) element)
a0, a1, a2, a3 = sp.symbols('a0 a1 a2 a3', real=True)
spinor = a0 + a1 * I1 + a2 * I2 + a3 * I3
print(f"\nGeneral Spinor Psi: {spinor}")

# Chiral polarization of light using Jones Matrices equivalent in GA
# Circular polarization basis
# Left circular
LCP = e1 + e2 * aps.i
# Right circular
RCP = e1 - e2 * aps.i

print("\n--- Chiral Polarization ---")
print(f"LCP: {LCP}")
print(f"RCP: {RCP}")

# Transformation via Jones matrix / Spinor rotor
# Quarter waveplate example (rotor)
theta = sp.pi / 4
rotor_qwp = sp.cos(theta) + I3 * sp.sin(theta)
print(f"\nQuarter Waveplate Rotor: {rotor_qwp}")

# Transform LCP
transformed_lcp = rotor_qwp * e1 * rotor_qwp.rev()
print(f"Transformed Field: {transformed_lcp}")
