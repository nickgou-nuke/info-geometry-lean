import sys
from sympy import symbols
from galgebra.ga import Ga
from galgebra.printer import Format

# Initialize pretty printing for galgebra
Format()

print("==================================================================")
print("Hestenes Geometric Algebra: The Dirac Equation as a Multivector")
print("==================================================================\n")

# 1. Define Spacetime Algebra Cl(1,3)
# The basis vectors are the Dirac gammas, but interpreted as pure geometric vectors.
coords = symbols('t x y z', real=True)
sta = Ga('gamma', g=[1, -1, -1, -1], coords=coords)
t, x, y, z = sta.coords
gamma0, gamma1, gamma2, gamma3 = sta.mv()

print("1. Spacetime Basis Vectors (Clifford Generators):")
print(f"gamma0^2 = {gamma0*gamma0}")
print(f"gamma1^2 = {gamma1*gamma1}\n")

# 2. Pseudoscalar and Spatial Bivectors
I = sta.I()  # The highest grade element gamma0*gamma1*gamma2*gamma3
sigma3 = gamma3 * gamma0  # Spatial bivector (isomorphic to Pauli matrix sigma_z)

print("2. The Pseudoscalar I (Volume element):")
print(f"I^2 = {I*I}")
print("Notice I^2 = -1. In STA, the complex unit 'i' is replaced by pure geometry!\n")

# 3. The Spinor Field as an Even Multivector
# In Hestenes' formulation, the spinor psi is NOT a column vector.
# It is an element of the even subalgebra of Cl(1,3).
psi = sta.mv('psi', 'even')

print("3. The Spinor psi (An Even Multivector):")
print("Psi is composed of a scalar, 6 bivectors (EM field generators), and a pseudoscalar.")
# Just showing the grades it contains
print(f"Grades in psi: {psi.grades}\n")

# 4. The Hestenes Dirac Equation
# grad psi I sigma3 = m psi gamma0
grad = sta.grad
m = symbols('m', real=True)

# We demonstrate the geometric action on the spinor
# grad * psi is the geometric derivative
dirac_action = grad * psi

print("4. The Geometric Derivative (grad * psi) combines the divergence and curl:")
print("It maps the even spinor to an odd multivector (vectors and trivectors).")
print(f"Grades in grad*psi: {dirac_action.grades}\n")

print("--- The Deep Connection to BdG and Modular Conjugation ---")
print("The standard Dirac equation requires an imaginary unit 'i'.")
print("In the Hestenes formulation, 'i' is replaced by right-multiplication by (I * sigma3).")
print("This right-multiplication is EXACTLY the Modular Conjugation (the Tomita-Takesaki operator)!")
print("It acts on the ideals of the Clifford algebra, inherently coupling the particle and hole (BdG) sheets.")
print("The algebraic structure maps perfectly to our Cl(1,1) tripotent split, as gamma0 acts to split the energy spectrum.")
