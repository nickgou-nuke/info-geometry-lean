import Mathlib.Tactic

open Finset
open scoped BigOperators

noncomputable section

namespace InfoGeometry.Canonical.DysonCoulombGas

/-!
# Dyson Coulomb Gas

This module records the finite algebraic bridge from a beta-2 Dyson gas
Hamiltonian to a Vandermonde-square expression once the analytic logarithm
facts are supplied explicitly.

## Proof surface

- BUCKET 1: finite definitions for external potential, log interaction,
  Hamiltonian, and Vandermonde product.
- BUCKET 2: `dyson_to_vandermonde_bridge` is conditional on the supplied
  product-to-sum logarithm identity and positivity of the Vandermonde product.
- BUCKET 3: no thermodynamic limit, random-matrix universality, zeta-zero
  statistics, or spectral theorem is asserted here.
-/

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

/--
The finite product-to-sum logarithm identity for the Vandermonde shadow.

The injectivity hypothesis is the exact finite exclusion condition needed to
ensure every nontrivial factor in the product is nonzero.
-/
theorem log_vandermonde_eq_sum_log (h_inj : Function.Injective lam) :
    Real.log (vandermonde_product lam) = log_interaction_energy lam := by
  unfold vandermonde_product log_interaction_energy
  have h_inner_nonzero :
      ∀ i : Fin N, (∏ j : Fin N, if i < j then |lam i - lam j| else 1) ≠ 0 := by
    intro i
    apply Finset.prod_ne_zero_iff.mpr
    intro j hj
    by_cases hij : i < j
    · have hne : lam i ≠ lam j := by
        intro hEq
        have hEqIdx : i = j := h_inj hEq
        exact (lt_irrefl _ (hEqIdx ▸ hij))
      have hdiff : lam i - lam j ≠ 0 := sub_ne_zero.mpr hne
      have habs : |lam i - lam j| ≠ 0 := abs_ne_zero.mpr hdiff
      simpa [hij] using habs
    · simp [hij]
  rw [Real.log_prod (fun i _ => h_inner_nonzero i)]
  congr with i
  have h_factor_nonzero :
      ∀ j : Fin N, (if i < j then |lam i - lam j| else 1) ≠ 0 := by
    intro j
    by_cases hij : i < j
    · have hne : lam i ≠ lam j := by
        intro hEq
        have hEqIdx : i = j := h_inj hEq
        exact (lt_irrefl _ (hEqIdx ▸ hij))
      have hdiff : lam i - lam j ≠ 0 := sub_ne_zero.mpr hne
      have habs : |lam i - lam j| ≠ 0 := abs_ne_zero.mpr hdiff
      simpa [hij] using habs
    · simp [hij]
  rw [Real.log_prod (fun j _ => h_factor_nonzero j)]
  congr with j
  split_ifs with hij <;> simp

/-- **Theorem (Dyson to Vandermonde Bridge)**:
    The finite beta-2 Coulomb repulsion rewrites as the negative logarithm of the
    Vandermonde product squared, provided the node map is injective. -/
theorem dyson_to_vandermonde_bridge (h_inj : Function.Injective lam) :
    dyson_hamiltonian lam V = external_potential_energy lam V - Real.log ((vandermonde_product lam) ^ 2) := by
  unfold dyson_hamiltonian
  rw [← log_vandermonde_eq_sum_log lam h_inj]
  rw [Real.log_pow]
  ring

end InfoGeometry.Canonical.DysonCoulombGas
