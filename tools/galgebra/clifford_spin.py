#!/usr/bin/env python3
"""
GAlgebra (Clifford/GA) code: Construct the Clifford algebra Cl(2) and
show that the even subalgebra is isomorphic to the complex numbers,
providing the complex structure on the tangent space of the hyper-Kähler
manifold Hilb_n(C^2). This illustrates the algebraic origin of the U(1)
action that appears in the equivariant parameters of the quantum K-theory
and is exchanged under 3d mirror symmetry.
"""

from galgebra.ga import Ga

# Build the Clifford algebra Cl(2) with signature (++), i.e., Euclidean R^2
# Basis vectors e1, e2 satisfy e1^2 = e2^2 = 1, e1*e2 = -e2*e1
(ga, e1, e2) = Ga.build('e1 e2', g=[1, 1])

# Display basis
print("Clifford algebra Cl(2) basis:")
print("  1           (grade 0)")
print("  e1, e2      (grade 1)")
print("  e12 = e1*e2 (grade 2)")

e12 = e1 * e2
print("\nElement e1*e2 =", e12)
print("(e1*e2)^2 =", e12 * e12)
print("Thus e1*e2 behaves like the imaginary unit i (square = -1).")

# The even subalgebra is spanned by {1, e1*e2}
print("\nEven subalgebra basis: {1, e1*e2}")
print("Any even element can be written as a + b*(e1*e2) with a,b in the base field.")
print("This is isomorphic to the complex numbers via a + b*i <-> a + b*(e1*e2).")

# Spin(2) consists of elements exp(theta/2 * e1*e2) for theta in [0, 2pi)
import sympy as sp
theta = sp.symbols('theta', real=True)
# For a bivector B with B^2 = -1, exp(theta/2 * B) = cos(theta/2) + sin(theta/2)*B
spin_expr = sp.cos(theta/2) + sp.sin(theta/2) * e12
print("\nSpin(2) element: exp(theta/2 * e1*e2) =", spin_expr)
print("This lies in the even subalgebra, hence acts as a complex phase.")
print("Thus Spin(2) ~ U(1) provides the natural U(1) action on the holomorphic symplectic form")
print("of Hilb_n(C^2). The U(1) action corresponds to the equivariant parameter in the")
print("quantum K-theory, and under 3d mirror symmetry the Kähler and equivariant parameters")
print("are exchanged.")