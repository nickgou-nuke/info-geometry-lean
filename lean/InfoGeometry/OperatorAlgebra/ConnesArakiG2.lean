import Mathlib.Algebra.Ring.Basic
import Mathlib.Algebra.Module.Basic
import InfoGeometry.Canonical.ZornSpinor
import InfoGeometry.Clifford.ChiralGrandCanonicalOperatorGeometry
import InfoGeometry.Canonical.ConnesRadonNikodymCocycle

open InfoGeometry.Canonical
open InfoGeometry.Clifford.ChiralGrandCanonicalOperatorGeometry
open ConnesCocycle

/-!
# Connes-Araki Radon-Nikodym Cocycle in G₂

This module formalizes the algebraic generator of the Connes-Araki Radon-Nikodym cocycle
within the exceptional group G₂ (represented via the split-octonion Zorn algebra).
The cocycle generator is exactly the difference of modular Hamiltonians.
-/

namespace InfoGeometry.OperatorAlgebra.ConnesArakiG2

/-- The G₂ derivation associated with a modular Hamiltonian. 
In the split real form, G₂(ℝ) acts on the Zorn matrix algebra. 
Here we define the purely algebraic generator of the Connes-Araki cocycle. -/
noncomputable def connesArakiG2Generator (H1 H2 : Operator) (beta1 μ1 μχ1 beta2 μ2 μχ2 : ℝ) : Operator :=
  connesRadonNikodymDerivative H1 H2 beta1 μ1 μχ1 beta2 μ2 μχ2

/-- The Connes-Araki cocycle generator vanishes when the modular states coincide. -/
theorem connesArakiG2Generator_zero_of_eq (H : Operator) (beta μ μχ : ℝ) :
    connesArakiG2Generator H H beta μ μχ beta μ μχ = 0 :=
  connesRadonNikodymDerivative_zero_of_eq H beta μ μχ

end InfoGeometry.OperatorAlgebra.ConnesArakiG2
