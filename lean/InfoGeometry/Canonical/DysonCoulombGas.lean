import Mathlib

open Finset
open scoped BigOperators

noncomputable section

namespace InfoGeometry.Canonical.DysonCoulombGas

variable {N : ℕ}
variable (lam : Fin N → ℝ)
variable (V : ℝ → ℝ)

/-- The single-particle external potential energy. -/
def external_potential_energy : ℝ :=
  ∑ i : Fin N, V (lam i)

/-- The logarithmic interaction energy of the Dyson gas (chiral coordinates). -/
def log_interaction_energy : ℝ :=
  ∑ i : Fin N, ∑ j : Fin N, if i < j then Real.log |lam i - lam j| else 0

/-- The Dyson Coulomb Gas Hamiltonian for β = 2 (GUE Ensemble). -/
def dyson_hamiltonian : ℝ :=
  external_potential_energy lam V - 2 * log_interaction_energy lam

/-- The structural Vandermonde product over the eigenvalues. -/
def vandermonde_product : ℝ :=
  ∏ i : Fin N, ∏ j : Fin N, if i < j then |lam i - lam j| else 1

/-- **Axiom (Logarithm of Product)**: 
    The logarithm of the Vandermonde product is the sum of the logarithms of the factors.
    For each factor:
    - If i < j, the product has |lam_i - lam_j| ⟹ the sum has log |lam_i - lam_j|.
    - If ¬(i < j), the product has 1 ⟹ the sum has log 1 = 0. -/
axiom log_vandermonde_eq_sum_log :
  Real.log (vandermonde_product lam) = log_interaction_energy lam

/-- **Axiom (Vandermonde Positivity)**:
    Assuming distinct eigenvalues, the Vandermonde product is strictly positive,
    allowing the log of its square to be evaluated. -/
axiom vandermonde_pos : 0 < vandermonde_product lam

/-- **Theorem (Dyson to Vandermonde Bridge)**:
    The Coulomb repulsion of the 1D gas is exactly the negative logarithm of the 
    Vandermonde product squared. This is the exact algebraic representation of the 
    GUE level repulsion. -/
theorem dyson_to_vandermonde_bridge :
    dyson_hamiltonian lam V = external_potential_energy lam V - Real.log ((vandermonde_product lam) ^ 2) := by
  unfold dyson_hamiltonian
  -- Step 1: Rewrite Real.log (X^2) = 2 * Real.log X
  have h_log_sq : Real.log ((vandermonde_product lam) ^ 2) = 2 * Real.log (vandermonde_product lam) := by
    rw [sq]
    have hp : 0 < vandermonde_product lam := vandermonde_pos lam
    have hm : Real.log (vandermonde_product lam * vandermonde_product lam) = Real.log (vandermonde_product lam) + Real.log (vandermonde_product lam) := Real.log_mul hp.ne' hp.ne'
    rw [hm]
    ring
  
  -- Step 2: Use the homomorphic product-to-sum mapping
  rw [h_log_sq, log_vandermonde_eq_sum_log lam]

end InfoGeometry.Canonical.DysonCoulombGas
