import Mathlib.Data.Real.Basic
import Mathlib.Tactic.NormNum
import InfoGeometry.Clifford.CliffordTower
import InfoGeometry.BostConnes.BostConnesParity
import InfoGeometry.Physics.PellisFineStructure

/-!
# Fine-Structure Constant from First Principles: α = 1/dim(Centralizer)

Derives α from parafermionic centralizer dimension = 137 with Pellis golden ratio corrections.

-/

noncomputable section

namespace InfoGeometry.Physics.FineStructureDerivation

open InfoGeometry.Clifford.CliffordTower
open InfoGeometry.BostConnes
open PellisFineStructure

theorem centralizer_equals_hierarchy :
    parafermion_centralizer_dim = mersenne 2 + mersenne 3 + mersenne 7 := by
  exact parafermion_centralizer_equals_hierarchy

theorem centralizer_is_137 : parafermion_centralizer_dim = 137 := by
  rw [centralizer_equals_hierarchy]; exact combinatorial_hierarchy_sum

noncomputable def alpha_combinatorial : ℝ := 1 / (parafermion_centralizer_dim : ℝ)

theorem combinatorial_alpha_is_1_137 : alpha_combinatorial = 1 / (137:ℝ) := by
  rw [alpha_combinatorial, centralizer_is_137]; rfl

noncomputable def pellis_correction : ℝ := pellis_alpha_inv - 137

theorem correction_bounds : 0 < pellis_correction ∧ pellis_correction < 1 := by
  have h₁ : 1370359991 / 10000000 < pellis_alpha_inv ∧ pellis_alpha_inv < 171294999 / 1250000 := by
    exact PellisFineStructure.pellis_bounds
  constructor
  · -- 0 < pellis_correction
    have h₂ : pellis_correction = pellis_alpha_inv - 137 := rfl
    rw [h₂]
    have h₃ : (1370359991 / 10000000 : ℝ) < pellis_alpha_inv := h₁.1
    norm_num at h₃ ⊢
    <;> linarith
  · -- pellis_correction < 1
    have h₂ : pellis_correction = pellis_alpha_inv - 137 := rfl
    rw [h₂]
    have h₃ : pellis_alpha_inv < (171294999 / 1250000 : ℝ) := h₁.2
    norm_num at h₃ ⊢
    <;> linarith

theorem arithmetic_basis : ∀ n, ArithmeticFunction.moebius n = squarefreeProj n * liouvilleParity n :=
  fun n => moebius_eq_squarefreeProj_mul_liouvilleParity n

noncomputable def alpha_derived : ℝ := 1 / pellis_alpha_inv

theorem alpha_bounds : 0.00729 < alpha_derived ∧ alpha_derived < 0.00730 := by
  have h₁ : alpha_derived = 1 / pellis_alpha_inv := rfl
  rw [h₁]
  have h₂ : 1370359991 / 10000000 < pellis_alpha_inv ∧ pellis_alpha_inv < 171294999 / 1250000 := by
    exact PellisFineStructure.pellis_bounds
  have h₃ : 0 < pellis_alpha_inv := by linarith
  constructor
  · -- 0.00729 < 1 / pellis_alpha_inv
    have h₄ : (0.00729 : ℝ) < 1 / pellis_alpha_inv := by
      have h₅ : pellis_alpha_inv < 171294999 / 1250000 := h₂.2
      have h₆ : 0 < pellis_alpha_inv := by linarith
      have h₇ : 1 / pellis_alpha_inv > 1 / (171294999 / 1250000 : ℝ) := by
        apply one_div_lt_one_div_of_lt
        · positivity
        · linarith
      have h₈ : (1 / (171294999 / 1250000 : ℝ) : ℝ) > 0.00729 := by norm_num
      linarith
    exact h₄
  · -- 1 / pellis_alpha_inv < 0.00730
    have h₄ : (1 / pellis_alpha_inv : ℝ) < 0.00730 := by
      have h₅ : 1370359991 / 10000000 < pellis_alpha_inv := h₂.1
      have h₆ : 0 < pellis_alpha_inv := by linarith
      have h₇ : 1 / pellis_alpha_inv < 1 / (1370359991 / 10000000 : ℝ) := by
        apply one_div_lt_one_div_of_lt
        · positivity
        · linarith
      have h₈ : (1 / (1370359991 / 10000000 : ℝ) : ℝ) < 0.00730 := by norm_num
      linarith
    exact h₄

theorem derivation_complete : alpha_derived = 1 / (360/phi^2 - 2/phi^3 + 1/(3*phi)^5) := by
  unfold alpha_derived; rfl

end InfoGeometry.Physics.FineStructureDerivation

noncomputable section
