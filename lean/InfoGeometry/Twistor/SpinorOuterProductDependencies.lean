/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/

import Mathlib.Data.Finset.Order
import Mathlib.Tactic
import Mathlib.Algebra.Star.Basic
import InfoGeometry.OperatorAlgebra.PeirceSpine.Basic
import InfoGeometry.OperatorAlgebra.PeirceSpine.Tetraktys

namespace InfoGeometry.Twistor.SpinorOuterProduct.ProofDependency

inductive Archetype
  | outerProduct
  | determinantNullity
  | hermitianDiagonal
  | scalarCovariance
  | phaseInvariance
  deriving DecidableEq

instance : Fintype Archetype where
  elems := {Archetype.outerProduct, Archetype.determinantNullity,
    Archetype.hermitianDiagonal, Archetype.scalarCovariance,
    Archetype.phaseInvariance}
  complete := by
    intro x
    cases x <;> simp

def prerequisites : Archetype → Finset ℕ
  | .outerProduct => {0}
  | .determinantNullity => {0, 1}
  | .hermitianDiagonal => {0, 2}
  | .scalarCovariance => {0, 3}
  | .phaseInvariance => {0, 3, 4}

theorem prerequisites_injective : Function.Injective prerequisites := by
  decide

instance : PartialOrder Archetype :=
  PartialOrder.lift prerequisites prerequisites_injective

instance : DecidableRel (α := Archetype) (· ≤ ·) :=
  fun left right => inferInstanceAs (Decidable (prerequisites left ⊆ prerequisites right))

theorem determinant_branch :
    Archetype.outerProduct ≤ Archetype.determinantNullity := by decide

theorem hermitian_branch :
    Archetype.outerProduct ≤ Archetype.hermitianDiagonal := by decide

theorem scaling_phase_branch :
    Archetype.outerProduct ≤ Archetype.scalarCovariance ∧
      Archetype.scalarCovariance ≤ Archetype.phaseInvariance := by decide

theorem nullity_and_phase_incomparable :
    ¬ Archetype.determinantNullity ≤ Archetype.phaseInvariance ∧
      ¬ Archetype.phaseInvariance ≤ Archetype.determinantNullity := by decide

theorem hermiticity_and_phase_incomparable :
    ¬ Archetype.hermitianDiagonal ≤ Archetype.phaseInvariance ∧
      ¬ Archetype.phaseInvariance ≤ Archetype.hermitianDiagonal := by decide

theorem no_cycle (left right : Archetype) (forward : left ≤ right)
    (backward : right ≤ left) : left = right :=
  le_antisymm forward backward

section NonCommutativeOperatorRealization

open InfoGeometry.OperatorAlgebra.PeirceSpine

variable {B : Type*} [Ring B]

/-- **Archetype 1 (`outerProduct`):**
Rank-one-type Peirce corner dyad `N_+ = P A (1 - P)` and its adjoint partner
`N_- = (1 - P) C P` satisfy `P * N_+ = N_+`, `N_+ * (1 - P) = N_+`, and
`(N_+ * N_-) * N_+ = V * N_+`. -/
theorem archetype_outerProduct_corner_dyad
    {P : B} (hP : P * P = P) (A C : B) :
    P * conePlus P A = conePlus P A ∧
    conePlus P A * (1 - P) = conePlus P A ∧
    (conePlus P A * coneMinus P C) * conePlus P A = genV P A C * conePlus P A := by
  refine ⟨?_, ?_, ?_⟩ <;> peirce_nf hP

/-- **Archetype 2 (`determinantNullity`):**
Null-square (isotropic determinant nullity) of the off-diagonal spinor dyads:
`N_+ * N_+ = 0`, `N_- * N_- = 0`, and `(N_+ * N_-) * (N_- * N_+) = 0`. -/
theorem archetype_determinantNullity_isotropic_dyad
    {P : B} (hP : P * P = P) (A C : B) :
    conePlus P A * conePlus P A = 0 ∧
    coneMinus P C * coneMinus P C = 0 ∧
    (conePlus P A * coneMinus P C) * (coneMinus P C * conePlus P A) = 0 ∧
    (coneMinus P C * conePlus P A) * (conePlus P A * coneMinus P C) = 0 := by
  refine ⟨?_, ?_, ?_, ?_⟩ <;> peirce_nf hP

/-- **Archetype 3 (`hermitianDiagonal`):**
In any `[StarRing B]` with `star P = P`, the diagonal Gram blocks `N_+ N_+^*` and `N_+^* N_+`
and their sum `V = N_+ N_+^* + N_+^* N_+` are self-adjoint (`star` Hermitian). -/
theorem archetype_hermitianDiagonal_gram_blocks
    [StarRing B] {P : B} (hPstar : star P = P) (A : B) :
    star (conePlus P A * coneMinus P (star A)) = conePlus P A * coneMinus P (star A) ∧
    star (coneMinus P (star A) * conePlus P A) = coneMinus P (star A) * conePlus P A ∧
    star (genV P A (star A)) = genV P A (star A) := by
  have h1 : star (conePlus P A) = coneMinus P (star A) := by
    simp only [conePlus, coneMinus, star_mul, star_sub, star_one, hPstar, mul_assoc]
  have h2 : star (coneMinus P (star A)) = conePlus P A := by
    simp only [conePlus, coneMinus, star_mul, star_sub, star_one, star_star, hPstar, mul_assoc]
  refine ⟨?_, ?_, ?_⟩
  · rw [star_mul, h1, h2]
  · rw [star_mul, h1, h2]
  · simp only [genV, anticomm, star_add, star_mul, h1, h2]

/-- **Archetype 4 (`scalarCovariance`):**
Bilinear operator-scaling covariance of the Peirce corners:
`peirce11 P X * conePlus P A = P * X * conePlus P A` and
`coneMinus P C * peirce11 P Y = coneMinus P C * Y * P`. -/
theorem archetype_scalarCovariance_module_scaling
    {P : B} (hP : P * P = P) (A C X Y : B) :
    peirce11 P X * conePlus P A = P * X * conePlus P A ∧
    coneMinus P C * peirce11 P Y = coneMinus P C * Y * P := by
  refine ⟨?_, ?_⟩ <;>
    (simp only [peirce11]; peirce_nf hP)

/-- **Archetype 5 (`phaseInvariance`):**
Invariance of the quadratic spinor Gram operators `V = {N_+, N_-}` and `Σ = [N_+, N_-]`
under the grading involution `S_P` and sign inversion `(N_+, N_-) ↦ (-N_+, -N_-)`:
`S_P * V * S_P = V`, `S_P * Σ * S_P = Σ`, and `{-N_+, -N_-} = V`. -/
theorem archetype_phaseInvariance_quadratic_gram
    {P : B} (hP : P * P = P) (A C : B) :
    invS P * genV P A C * invS P = genV P A C ∧
    invS P * genSig P A C * invS P = genSig P A C ∧
    anticomm (-conePlus P A) (-coneMinus P C) = genV P A C := by
  refine ⟨?_, ?_, ?_⟩ <;> peirce_nf hP

/-- **Master Synthesis (`spinor_outer_product_dependencies_master_synthesis`):**
Unites the partial-order branch theorems with all five `[Ring B] [StarRing B]`
spinor outer-product operator theorems. -/
theorem spinor_outer_product_dependencies_master_synthesis
    [StarRing B] {P : B} (hP : P * P = P) (hPstar : star P = P) (A X Y : B) :
    (Archetype.outerProduct ≤ Archetype.determinantNullity ∧
      Archetype.outerProduct ≤ Archetype.hermitianDiagonal ∧
      Archetype.outerProduct ≤ Archetype.scalarCovariance ∧
      Archetype.scalarCovariance ≤ Archetype.phaseInvariance) ∧
    ((conePlus P A * coneMinus P (star A)) * conePlus P A =
      genV P A (star A) * conePlus P A) ∧
    ((conePlus P A * coneMinus P (star A)) * (coneMinus P (star A) * conePlus P A) = 0) ∧
    (star (genV P A (star A)) = genV P A (star A)) ∧
    (peirce11 P X * conePlus P A = P * X * conePlus P A) ∧
    (invS P * genV P A (star A) * invS P = genV P A (star A)) := by
  have h1 := archetype_outerProduct_corner_dyad hP A (star A)
  have h2 := archetype_determinantNullity_isotropic_dyad hP A (star A)
  have h3 := archetype_hermitianDiagonal_gram_blocks hPstar A
  have h4 := archetype_scalarCovariance_module_scaling hP A (star A) X Y
  have h5 := archetype_phaseInvariance_quadratic_gram hP A (star A)
  exact ⟨⟨determinant_branch, hermitian_branch, scaling_phase_branch⟩,
    h1.2.2, h2.2.2.1, h3.2.2, h4.1, h5.1⟩

end NonCommutativeOperatorRealization

end InfoGeometry.Twistor.SpinorOuterProduct.ProofDependency
