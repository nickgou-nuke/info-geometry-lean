#!/usr/bin/env python3
# -*- coding: utf-8 -*-
"""
GAlgebra/Clifford sketch for the First Law of Modular Thermodynamics.

We illustrate how the exponential structure of the density matrix ρ = e^{-K}/Q
connects to geometric algebra, particularly through the interpretation of 
the modular Hamiltonian K as a generator of flows in spacetime algebra.

In relativistic quantum field theory, the modular Hamiltonian for certain 
regions (e.g., wedge domains) takes the form K = ∫_Σ ξ^μ T_{μν} dΣ^ν,
where ξ is a Killing vector field generating a flow (like a boost rotation).
Such generators can be naturally represented as bivectors or vectors in 
geometric algebra, where exponentials give rotors or boosters.

We demonstrate this by:
1. Constructing a spacetime algebra (Cl(3,1) or Cl(1,3))
2. Showing how a generator like a boost (analogous to modular flow) 
   exponentiates to a rotor
3. Connecting this to the structure e^{-K} in the density matrix
"""

from galgebra.ga import Ga
import math

# For simplicity, we work in 2D Minkowski space (can be extended to 4D)
# Basis: e0 (time), e1 (space)
# Metric: η = diag(-1, 1) for (+,-,-,-) signature or diag(1,-1) for (-,+,+,+)
# We'll use (+,-,-,-) signature: η = [[1,0],[0,-1]] -> g=[1,-1]

print("=== Geometric Algebra Interpretation of Modular Structure ===\n")

# Build 2D Minkowski geometric algebra
# Signature [1, -1] corresponds to e0^2 = 1, e1^2 = -1
ga = Ga = Ga('e0 e1', g=[1, -1])
e0, e1 = ga.mv()

print("Basis vectors:")
print(f'dx^2 = {e0*e0}')  # Should be 1
print(f"  e1^2 = {e1*e1}")  # Should be -1
print(f"  e0·e1 = {(e0*e1 + e1*e0)/2}")  # Should be 0
print()

# The Minkowski pseudo-scalar (volume element)
I = e0 ^ e1  # wedge product
print(f"Pseudo-scalar I = e0^e1 = {I}")
print(f"I^2 = {I*I}")  # Should be -1
print()

# A boost generator in the x-direction can be represented as 
# K = η * e0^e1 (where η is rapidity)
# This is analogous to how the modular Hamiltonian generates flow
eta_val = 0.5  # example value (rapidity)
K_gen = eta_val * (e0 ^ e1)  # bivector generator

print(f"Boost generator (analogous to modular Hamiltonian):")
print(f"  K = η (e0^e1) = {K_gen}")
print()

# The exponential of a bivector gives a rotor (Lorentz boost)
# exp(-K) = exp(-η e0^e1) = cosh(η) - sinh(η) e0^e1
minus_K = -K_gen
try:
    exp_minus_K = (-K_gen).exp()  # This computes exp(-K)
    print(f"exp(-K) = exp(-η e0^e1) = {exp_minus_K}")
except Exception as e:
    print(f"Error computing exponential: {e}")
    # Manual computation using the formula for bivector exponential
    # For a bivector B where B^2 = -a^2 (scalar), exp(B) = cosh(|B|) + (B/|B|) sinh(|B|)
    # Here, K_gen^2 = (eta_val^2) * (e0^e1)^2 = eta_val^2 * (-1) = -eta_val^2
    # So |K| = eta_val
    scalar_part = math.cosh(eta_val)
    bivector_part = - (e0 ^ e1) * math.sinh(eta_val)  # negative for -K
    exp_minus_K = scalar_part + bivector_part
    print(f"exp(-K) (manual) = {exp_minus_K}")

print()

# Expected result: cosh(η) - sinh(η) e0^e1
expected_scalar = math.cosh(eta_val)
expected_bivector_coeff = -math.sinh(eta_val)
print(f"Expected: cosh({eta_val}) - sinh({eta_val}) e0^e1")
print(f"          = {expected_scalar} - ({expected_bivector_coeff}) e0^e1")
print()

# This connects to the density matrix form: ρ = e^{-K}/Tr(e^{-K})
# In the algebraic setting, the trace operation corresponds to 
# extracting the scalar part in certain representations
print("Connection to density matrix:")
print("  In quantum statistical mechanics: ρ = e^{-K}/Tr(e^{-K})")
print("  In geometric algebra terms:")
print("    - The exponential e^{-K} is a rotor (for K as bivector generator)")
print("    - The trace operation corresponds to taking the scalar part")
print("    - Normalization ensures the scalar part equals 1 after division")
print()

print("First Law of Modular Thermodynamics connection:")
print("  When we vary the state (change rapidity η),")
print("  the variation of entropy dS equals variation of expectation d⟨K⟩")
print("  This reflects how changes in the geometric structure (encoded in K)")
print("  directly correspond to changes in information-theoretic entropy.")
print()

print("Note: A full implementation would require:")
print("  - Defining the algebra of observables (as a subalgebra of the Clifford algebra)")
print("  - Defining the state functional and entropy measure")
print("  - Showing that the modular automorphism group is implemented by")
print("    conjugation with exp(tK/2) in the algebra")
print("  - Verifying that dS = d⟨K⟩ holds for variations within this framework")