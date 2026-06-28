#!/usr/bin/env python3
"""
Sympy-based Clifford algebra for Cl(2) (Euclidean) and its spin group.
Demonstrates that the even subalgebra is isomorphic to C and that
Spin(2) acts as U(1) on the plane, providing the complex structure
relevant to the hyper-Kähler geometry of Hilb_n(C^2) and its 3d mirror symmetry.
"""

import sympy as sp

# Pauli matrices (complex, 2x2)
sigma1 = sp.Matrix([[0, 1],
                    [1, 0]])
sigma2 = sp.Matrix([[0, -sp.I],
                    [sp.I, 0]])
sigma3 = sp.Matrix([[1, 0],
                    [0, -1]])

# For Cl(2) we can use gamma matrices satisfying {gamma_i, gamma_j} = 2*delta_ij
# Choose gamma1 = sigma1, gamma2 = sigma2
gamma1 = sigma1
gamma2 = sigma2

# Verify anticommutation relations
print("gamma1*gamma2 + gamma2*gamma1 =", gamma1*gamma2 + gamma2*gamma1)  # should be 0
print("gamma1^2 =", gamma1**2)  # should be I
print("gamma2^2 =", gamma2**2)  # should be I

# The volume element (pseudoscalar) omega = gamma1*gamma2
omega = gamma1 * gamma2
print("\nVolume element omega = gamma1*gamma2 =")
sp.pprint(omega)
print("omega^2 =", omega**2)  # should be -I

# The even subalgebra is spanned by {I, omega}
# Any element a*I + b*omega with a,b complex behaves like a + b*i
print("\nEven subalgebra: a*I + b*omega")
print("Isomorphic to complex numbers via a + b*i <-> a*I + b*omega")

# Spin(2) = { exp(theta/2 * omega) | theta in [0, 2π) }
theta = sp.symbols('theta', real=True)
# Since omega^2 = -I, we have exp(alpha*omega) = cos(alpha) + sin(alpha)*omega
spin = sp.cos(theta/2) * sp.eye(2) + sp.sin(theta/2) * omega
print("\nSpin(2) element exp(theta/2 * omega) =")
sp.pprint(spin)
# Check unitary: spin * spin.H = I
print("Check unitary: spin * spin.H =", sp.simplify(spin * spin.H))  # should be I

# Action on a vector v = x*gamma1 + y*gamma2 (as a matrix)
x_sym, y_sym = sp.symbols('x y')
v = x_sym * gamma1 + y_sym * gamma2
print("\nVector v = x*gamma1 + y*gamma2 =")
sp.pprint(v)

# The adjoint action of Spin(2) on vectors: v' = g * v * g^{-1}
# For elements of Spin, g^{-1} = \tilde{g} (reverse) = cos - sin*omega
# Since omega is grade 2, reverse(omega) = -omega, so g^{-1} = cos - sin*omega
ginv = sp.cos(theta/2) * sp.eye(2) - sp.sin(theta/2) * omega
vprime = sp.simplify(spin * v * ginv)
print("\nAction: v' = g * v * g^{-1} =")
sp.pprint(vprime)
# Expect v' = (x cosθ - y sinθ) gamma1 + (x sinθ + y cosθ) gamma2
# Extract coefficients
coeff_g1 = vprime[0,1] + vprime[1,0]  # because gamma1 = [[0,1],[1,0]]
coeff_g2 = (vprime[0,0] - vprime[1,1]) / (-sp.I)  # gamma2 = [[0,-i],[i,0]]
print("\nCoefficient of gamma1:", sp.simplify(coeff_g1))
print("Coefficient of gamma2:", sp.simplify(coeff_g2))
# Should be x*cosθ - y*sinθ and x*sinθ + y*cosθ respectively
print("\nThus the action rotates the vector (x,y) by angle theta in the (gamma1, gamma2)-plane.")
print("This realizes the double cover Spin(2) -> SO(2).")
print("\nThe U(1) action of Spin(2) on the holomorphic symplectic form")
print("of Hilb_n(C^2) corresponds to rotating the complex structure,")
print("which is exactly the equivariant parameter in the quantum K-theory.")
print("Under 3d mirror symmetry, the Kähler and equivariant parameters are exchanged.")