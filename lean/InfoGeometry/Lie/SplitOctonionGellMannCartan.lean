import InfoGeometry.Lie.SplitOctonionAxialCartanDerivation
import InfoGeometry.Algebra.FiniteSpinAlgebra
import InfoGeometry.Lie.SplitOctonionCartanSixWeights
import InfoGeometry.Lie.SplitOctonionAxialCartanErlangen
import Mathlib.Tactic

/-!
# Gell-Mann Weight Readout for the Split-Octonion Cartan Action

This file formalizes the exact Cartan action of `G_{2(2)}` in the Gell-Mann
basis representation, specifically as:
`H = K₁ Λ₃ + K₂ Λ₈`

The weights are represented as `k = K₁ (1, -1, 0) + K₂ (1, 1, -2)`.
This corresponds directly to the `G_{2(2)}` Cartan plane.
-/

namespace InfoGeometry.Lie.SplitOctonionGellMannCartan

open InfoGeometry.Canonical.ZornMatrix
open InfoGeometry.Lie.SplitOctonionAxialCartanDerivation
open InfoGeometry.Lie.SplitOctonionAxialCartanErlangen
open InfoGeometry.Lie.SplitOctonionCartanSixWeights
open InfoGeometry.Lie.SplitOctonionQuaternionZornCoordinates
open InfoGeometry.Lie.SplitOctonionQuaternionCircularBasis

open scoped BigOperators

/-- The `Λ₃` Gell-Mann Cartan generator weights `(1, -1, 0)`. -/
def lambda3Weights : Fin 3 → ℝ :=
  fun i => if i.val = 0 then 1 else if i.val = 1 then -1 else 0

/-- The `Λ₃` generator weights are traceless. -/
theorem lambda3Weights_sum_zero : weightSum lambda3Weights = 0 := by
  change ∑ i : Fin 3, lambda3Weights i = 0
  rw [Fin.sum_univ_three]
  change (1 : ℝ) + -1 + 0 = 0
  norm_num

/-- The traceless `Λ₃` weight vector. -/
def lambda3Traceless : TracelessWeight :=
  ⟨lambda3Weights, lambda3Weights_sum_zero⟩

/-- The `Λ₈` Gell-Mann Cartan generator weights `(1, 1, -2)`. -/
def lambda8Weights : Fin 3 → ℝ :=
  fun i => if i.val = 0 then 1 else if i.val = 1 then 1 else -2

noncomputable def lambda3Matrix : Matrix (Fin 3) (Fin 3) ℝ :=
  Matrix.diagonal lambda3Weights

noncomputable def lambda8Matrix : Matrix (Fin 3) (Fin 3) ℝ :=
  Matrix.diagonal lambda8Weights

/-- The `Λ₈` generator weights are traceless. -/
theorem lambda8Weights_sum_zero : weightSum lambda8Weights = 0 := by
  change ∑ i : Fin 3, lambda8Weights i = 0
  rw [Fin.sum_univ_three]
  change (1 : ℝ) + 1 + -2 = 0
  norm_num

/-- The traceless `Λ₈` weight vector. -/
def lambda8Traceless : TracelessWeight :=
  ⟨lambda8Weights, lambda8Weights_sum_zero⟩

/-- The general Cartan action `H = K₁ Λ₃ + K₂ Λ₈` as a traceless weight vector. -/
def gellMannCartan (K1 K2 : ℝ) : TracelessWeight :=
  K1 • lambda3Traceless + K2 • lambda8Traceless

/-- The explicit coordinate evaluation of the Gell-Mann Cartan action. -/
theorem gellMannCartan_apply (K1 K2 : ℝ) (i : Fin 3) :
    (gellMannCartan K1 K2).val i =
      K1 * (if i.val = 0 then 1 else if i.val = 1 then -1 else 0) +
      K2 * (if i.val = 0 then 1 else if i.val = 1 then 1 else -2) := by
  change K1 * lambda3Weights i + K2 * lambda8Weights i = _
  rfl

/-! The following matrix is the real diagonal weight readout.  We use the
unnormalized `Λ₈` convention `(1,1,-2)`; the physics normalization is obtained
by replacing `K2` with `K2 / Real.sqrt 3`. -/
noncomputable def gellMannCartanMatrix (K1 K2 : ℝ) :
    Matrix (Fin 3) (Fin 3) ℝ :=
  Matrix.diagonal (gellMannCartan K1 K2).1

theorem gellMannCartanMatrix_apply (K1 K2 : ℝ) (i : Fin 3) :
    gellMannCartanMatrix K1 K2 i i =
      K1 * (if i.val = 0 then 1 else if i.val = 1 then -1 else 0) +
      K2 * (if i.val = 0 then 1 else if i.val = 1 then 1 else -2) := by
  simp [gellMannCartanMatrix, gellMannCartan_apply]

theorem gellMannCartanMatrix_offdiag (K1 K2 : ℝ) {i j : Fin 3}
    (h : i ≠ j) : gellMannCartanMatrix K1 K2 i j = 0 := by
  simp [gellMannCartanMatrix, h]

theorem gellMannCartanMatrix_trace (K1 K2 : ℝ) :
    Matrix.trace (gellMannCartanMatrix K1 K2) = 0 := by
  change ∑ i : Fin 3, (gellMannCartan K1 K2).1 i = 0
  exact (gellMannCartan K1 K2).2

theorem gellMannCartanMatrix_eq_linear_combination (K1 K2 : ℝ) :
    gellMannCartanMatrix K1 K2 =
      K1 • lambda3Matrix + K2 • lambda8Matrix := by
  ext i j
  by_cases h : i = j
  · subst j
    simp [gellMannCartanMatrix, lambda3Matrix, lambda8Matrix,
      gellMannCartan_apply, lambda3Weights, lambda8Weights]
  · simp [gellMannCartanMatrix, lambda3Matrix, lambda8Matrix, h]

theorem axialCartanEnd_gellMann_rootPlus (K1 K2 : ℝ) (i : Fin 3) :
    axialCartanEnd (gellMannCartan K1 K2).1
        (cartesianZornLinearEquiv (rootPlus i)) =
      (gellMannCartan K1 K2).1 i •
        cartesianZornLinearEquiv (rootPlus i) := by
  exact axialCartanEnd_rootPlus (gellMannCartan K1 K2).1 i

theorem axialCartanEnd_gellMann_rootMinus (K1 K2 : ℝ) (i : Fin 3) :
    axialCartanEnd (gellMannCartan K1 K2).1
        (cartesianZornLinearEquiv (rootMinus i)) =
      -((gellMannCartan K1 K2).1 i) •
        cartesianZornLinearEquiv (rootMinus i) := by
  exact axialCartanEnd_rootMinus (gellMannCartan K1 K2).1 i

/-- The Gell-Mann Cartan parameters `K₁` and `K₂` span the entire 2D traceless space. -/
theorem gellMannCartan_surjective (k : TracelessWeight) : ∃ K1 K2 : ℝ, gellMannCartan K1 K2 = k := by
  use (k.val 0 - k.val 1) / 2
  use -k.val 2 / 2
  apply Subtype.ext
  ext i
  rw [gellMannCartan_apply]
  have hsum : k.val 0 + k.val 1 + k.val 2 = 0 := by
    have hk := k.2
    change ∑ i : Fin 3, k.val i = 0 at hk
    rw [Fin.sum_univ_three] at hk
    exact hk
  fin_cases i
  · change ((k.val 0 - k.val 1) / 2) * 1 + (-k.val 2 / 2) * 1 = k.val 0
    linarith
  · change ((k.val 0 - k.val 1) / 2) * -1 + (-k.val 2 / 2) * 1 = k.val 1
    linarith
  · change ((k.val 0 - k.val 1) / 2) * 0 + (-k.val 2 / 2) * -2 = k.val 2
    linarith

end InfoGeometry.Lie.SplitOctonionGellMannCartan
