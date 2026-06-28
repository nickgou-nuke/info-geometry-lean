import InfoGeometry.Physics.ZornNuclearState
import Mathlib.GroupTheory.Perm.Basic
import Mathlib.Tactic.Ring
import Mathlib.Data.Finset.Basic

/-!
Formalization of D₄ Triality and its S₃ Action on Zorn Algebras.
This module defines the S₃ permutation of the 8-dimensional representations
and proves its consistency with the 5-graded structure.
-/

namespace InfoGeometry.Physics

/-- Triality as an S₃ permutation on the three 8D representation branches -/
structure TrialityAction where
  perm : Equiv.Perm (Fin 3) -- Permutation of {0, 1, 2}

/-- The S₃ action on a Zorn matrix permuting the quark/antiquark colors -/
def TrialityAction.apply (τ : TrialityAction) (Z : ZornMatrix) : ZornMatrix :=
  { a := Z.a
    b := Z.b
    x := fun i => Z.x (τ.perm i)
    y := fun i => Z.y (τ.perm i) }

/-- The tripotent operator on Zorn matrices: T(Z) = (0, 0, x, -y) -/
def ZornMatrix.tripotent (Z : ZornMatrix) : ZornMatrix :=
  { a := 0
    b := 0
    x := Z.x
    y := fun i => -Z.y i }

/-- Theorem: Triality preserves the Zorn determinant -/
theorem TrialityAction.preserves_det (τ : TrialityAction) (Z : ZornMatrix) :
    (τ.apply Z).det = Z.det := by
  simp [TrialityAction.apply, ZornMatrix.det]
  -- The determinant involves a sum over Fin 3 which is invariant under permutation
  have h_sum : (∑ i : Fin 3, Z.x (τ.perm i) * Z.y (τ.perm i)) = (∑ j : Fin 3, Z.x j * Z.y j) := by
    -- Use the fact that permutation of indices in a finite sum doesn't change the sum
    have h₂ : ∑ i : Fin 3, (Z.x (τ.perm i) * Z.y (τ.perm i)) = ∑ i : Fin 3, (Z.x i * Z.y i) := by
      -- The function being summed is (fun i => Z.x i * Z.y i) ∘ τ.perm
      -- Since τ.perm is a permutation, the sum is invariant
      rw [Finset.sum_equiv (τ.perm)]
      <;> simp [Equiv.Perm.sign]
    rw [h₂]
    <;> rfl
  rw [h_sum]
  <;> rfl

/-- Theorem: Triality preserves the tripotent operator (grading preservation) -/
theorem TrialityAction.commutes_with_tripotent (τ : TrialityAction) (Z : ZornMatrix) :
  (τ.apply (ZornMatrix.tripotent Z)) = ZornMatrix.tripotent (τ.apply Z) := by
  simp [TrialityAction.apply, ZornMatrix.tripotent]
  <;> ext <;> simp [Equiv.Perm.sign]
  <;>
  (try aesop)
  <;>
  (try
    {
      fin_cases τ.perm <;>
      simp_all [Equiv.Perm.sign, Fin.val_zero, Fin.val_one, Fin.val_two] <;>
      aesop
    })

end InfoGeometry.Physics
