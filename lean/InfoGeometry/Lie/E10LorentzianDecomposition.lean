import Mathlib.Data.Real.Basic
import Mathlib.Tactic
import InfoGeometry.Lie.E10TimelikeWitness

/-!
# Completing squares in the E₁₀ Cartan form

The E₁₀ diagram has three A-type arms of lengths 1, 2, and 6 at its central
node. Completing squares along those arms expresses the form as an explicit
nonnegative arm contribution minus the central coordinate squared over 42.
This is stronger than exhibiting a single negative vector. The identity alone
does not count the inertia or prove the separate strict-hyperbolicity
subdiagram criterion.
-/

namespace InfoGeometry.Lie.E10LorentzianDecomposition

open InfoGeometry.Lie.E10

/-- Shifted coordinate on the one-node arm. -/
noncomputable def a1 (x : Fin 10 → ℝ) : ℝ := x 1 - x 0 / 2

/-- Shifted coordinates on the two-node arm. -/
noncomputable def a2 (x : Fin 10 → ℝ) : ℝ := x 2 - (2 / 3 : ℝ) * x 0
noncomputable def a3 (x : Fin 10 → ℝ) : ℝ := x 3 - x 0 / 3

/-- Shifted coordinates on the six-node arm. -/
noncomputable def a4 (x : Fin 10 → ℝ) : ℝ := x 4 - (6 / 7 : ℝ) * x 0
noncomputable def a5 (x : Fin 10 → ℝ) : ℝ := x 5 - (5 / 7 : ℝ) * x 0
noncomputable def a6 (x : Fin 10 → ℝ) : ℝ := x 6 - (4 / 7 : ℝ) * x 0
noncomputable def a7 (x : Fin 10 → ℝ) : ℝ := x 7 - (3 / 7 : ℝ) * x 0
noncomputable def a8 (x : Fin 10 → ℝ) : ℝ := x 8 - (2 / 7 : ℝ) * x 0
noncomputable def a9 (x : Fin 10 → ℝ) : ℝ := x 9 - x 0 / 7

/-- Sum of the positive arm forms after shifting away the central coordinate. -/
noncomputable def positiveArmPart (x : Fin 10 → ℝ) : ℝ :=
  2 * a1 x ^ 2 + a2 x ^ 2 + (a2 x - a3 x) ^ 2 + a3 x ^ 2 +
    a4 x ^ 2 + (a4 x - a5 x) ^ 2 + (a5 x - a6 x) ^ 2 +
    (a6 x - a7 x) ^ 2 + (a7 x - a8 x) ^ 2 + (a8 x - a9 x) ^ 2 + a9 x ^ 2

/-- The real E₁₀ Cartan quadratic form, with the matrix entries coerced to ℝ. -/
def cartanQuadraticFormReal (x : Fin 10 → ℝ) : ℝ :=
  ∑ i : Fin 10, ∑ j : Fin 10, x i * (cartanMatrix i j : ℝ) * x j

/-- Expanded polynomial for the E₁₀ diagram with central node `0` and arms
`0—1`, `0—2—3`, and `0—4—5—6—7—8—9`. -/
def cartanFormExpanded (x : Fin 10 → ℝ) : ℝ :=
  2 * (x 0) ^ 2 + 2 * (x 1) ^ 2 + 2 * (x 2) ^ 2 + 2 * (x 3) ^ 2 +
    2 * (x 4) ^ 2 + 2 * (x 5) ^ 2 + 2 * (x 6) ^ 2 + 2 * (x 7) ^ 2 +
    2 * (x 8) ^ 2 + 2 * (x 9) ^ 2 - 2 * (x 0) * (x 1) -
    2 * (x 0) * (x 2) - 2 * (x 2) * (x 3) - 2 * (x 0) * (x 4) -
    2 * (x 4) * (x 5) - 2 * (x 5) * (x 6) - 2 * (x 6) * (x 7) -
    2 * (x 7) * (x 8) - 2 * (x 8) * (x 9)

/-- The matrix contraction reduces to the polynomial read directly from the
E₁₀ diagram. -/
theorem cartanQuadraticFormReal_eq_expanded (x : Fin 10 → ℝ) :
    cartanQuadraticFormReal x = cartanFormExpanded x := by
  simp [cartanQuadraticFormReal, cartanFormExpanded, cartanMatrix, Adjacent, edges,
    Fin.sum_univ_succ]
  ring

/-- Completing squares along all three arms leaves the Schur complement `-1/42`
at the trivalent vertex. -/
theorem cartan_form_eq_arm_squares_sub_central (x : Fin 10 → ℝ) :
    cartanQuadraticFormReal x = positiveArmPart x - (x 0) ^ 2 / 42 := by
  rw [cartanQuadraticFormReal_eq_expanded]
  simp [cartanFormExpanded, positiveArmPart, a1, a2, a3, a4, a5, a6, a7, a8, a9]
  field_simp; ring

/-- Every arm contribution is nonnegative. -/
theorem positiveArmPart_nonneg (x : Fin 10 → ℝ) : 0 ≤ positiveArmPart x := by
  simp only [positiveArmPart]
  positivity

/-- On the hyperplane where the central coordinate vanishes, the Cartan form
is nonnegative. -/
theorem central_zero_form_nonneg (x : Fin 10 → ℝ) (h : x 0 = 0) :
    0 ≤ cartanQuadraticFormReal x := by
  rw [cartan_form_eq_arm_squares_sub_central]
  simp [h]
  exact positiveArmPart_nonneg x

/-- The central coordinate and the positive arm contribution give the
completed-square expression. -/
theorem completed_square_decomposition (x : Fin 10 → ℝ) :
    cartanQuadraticFormReal x = positiveArmPart x - (x 0) ^ 2 / 42 :=
  cartan_form_eq_arm_squares_sub_central x

end InfoGeometry.Lie.E10LorentzianDecomposition
