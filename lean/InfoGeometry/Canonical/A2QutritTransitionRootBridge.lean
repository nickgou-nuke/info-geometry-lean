import Mathlib
import InfoGeometry.Algebra.FiniteSpinAlgebra
import InfoGeometry.Canonical.A2InsideD5RootSubsystem
import InfoGeometry.Canonical.TwoSheetThreeColorWeyl

/-!
# The `A₂` transition-root realization on the qutrit carrier

The six ordered `A₂` roots are realized here by the six off-diagonal
matrix units of `M₃(ℂ)`.  This is a concrete matrix bridge: it does not
package a witness structure or assert a representation by contract.
-/

noncomputable section

namespace InfoGeometry.Canonical.A2QutritTransitionRootBridge

open Matrix
open InfoGeometry.Canonical.A2InsideD5RootSubsystem

abbrev QutritMatrix := InfoGeometry.Algebra.FiniteSpin.QutritMatrix

/-- The qutrit transition matrix attached to an ordered pair of distinct levels. -/
def transitionMatrix (r : A2Root) : QutritMatrix :=
  Matrix.single r.1.1 r.1.2 1

/-- The diagonal Cartan matrix with eigenvalue function `h`. -/
def diagonalCartan (h : Fin 3 → ℂ) : QutritMatrix := Matrix.diagonal h

@[simp] theorem transitionMatrix_apply_source_target (r : A2Root) :
    transitionMatrix r r.1.1 r.1.2 = 1 := by
  simp [transitionMatrix]

theorem transitionMatrix_ne_zero (r : A2Root) :
    transitionMatrix r ≠ 0 := by
  intro h
  have hentry := congrArg (fun M : QutritMatrix => M r.1.1 r.1.2) h
  simp [transitionMatrix] at hentry

theorem transitionMatrix_injective :
    Function.Injective transitionMatrix := by
  intro r s h
  apply Subtype.ext
  apply Prod.ext
  · by_contra hne
    have hentry := congrArg (fun M : QutritMatrix =>
      M r.1.1 r.1.2) h
    have hne' : s.1.1 ≠ r.1.1 := by
      intro hs
      exact hne hs.symm
    simp [transitionMatrix, Matrix.single, hne'] at hentry
  · have hi : r.1.1 = s.1.1 := by
      by_contra hne
      have hentry := congrArg (fun M : QutritMatrix =>
        M r.1.1 r.1.2) h
      have hne' : s.1.1 ≠ r.1.1 := by
        intro hs
        exact hne hs.symm
      simp [transitionMatrix, Matrix.single, hne'] at hentry
    have hentry := congrArg (fun M : QutritMatrix =>
      M r.1.1 r.1.2) h
    by_contra hne
    have hne' : s.1.2 ≠ r.1.2 := by
      intro hs
      exact hne hs.symm
    simp [transitionMatrix, Matrix.single, hi, hne'] at hentry

theorem transitionMatrix_card :
    Fintype.card (Set.range transitionMatrix) = 6 := by
  have hcard :=
    Fintype.card_congr
      (Equiv.ofInjective transitionMatrix transitionMatrix_injective)
  simpa using hcard.symm

def oppositeRoot (r : A2Root) : A2Root :=
  ⟨(r.1.2, r.1.1), by
    intro h
    exact r.2 h.symm⟩

@[simp] theorem oppositeRoot_involutive (r : A2Root) :
    oppositeRoot (oppositeRoot r) = r := by
  apply Subtype.ext
  rfl

theorem oppositeRoot_injective : Function.Injective oppositeRoot := by
  intro r s h
  calc
    r = oppositeRoot (oppositeRoot r) := (oppositeRoot_involutive r).symm
    _ = oppositeRoot (oppositeRoot s) := by rw [h]
    _ = s := oppositeRoot_involutive s

theorem oppositeRoot_weylAction_commute
    (σ : Equiv.Perm (Fin 3)) (r : A2Root) :
    oppositeRoot (weylAction σ r) =
      weylAction σ (oppositeRoot r) := by
  apply Subtype.ext
  rfl

theorem a2RootVector_opposite (r : A2Root) :
    a2RootVector (oppositeRoot r) = -a2RootVector r := by
  funext k
  simp [a2RootVector, oppositeRoot, coordinate, embed3,
    sub_eq_add_neg]

theorem transitionMatrix_opposite_conjTranspose (r : A2Root) :
    transitionMatrix (oppositeRoot r) = (transitionMatrix r)ᴴ := by
  ext i j
  simp [oppositeRoot, transitionMatrix, Matrix.conjTranspose,
    Matrix.single, and_comm]

theorem transitionMatrix_opposite_transpose (r : A2Root) :
    transitionMatrix (oppositeRoot r) = Matrix.transpose (transitionMatrix r) := by
  ext i j
  simp [oppositeRoot, transitionMatrix, Matrix.transpose, Matrix.single,
    and_comm]

theorem forward_transition_sum_eq_colorShift_sq :
    ∑ i : Fin 3, transitionMatrix (rootFromIndex i) =
      InfoGeometry.Canonical.TwoSheetThreeColorWeyl.colorShift ^ 2 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [transitionMatrix, rootFromIndex, next3,
      InfoGeometry.Canonical.TwoSheetThreeColorWeyl.colorShift,
      Matrix.sum_apply, Fin.sum_univ_three, Matrix.single, pow_two,
      Matrix.mul_apply] <;>
    native_decide

theorem reverse_transition_sum_eq_colorShift :
    ∑ i : Fin 3, transitionMatrix (oppositeRoot (rootFromIndex i)) =
      InfoGeometry.Canonical.TwoSheetThreeColorWeyl.colorShift := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [transitionMatrix, oppositeRoot, rootFromIndex, next3,
      InfoGeometry.Canonical.TwoSheetThreeColorWeyl.colorShift,
      Matrix.sum_apply, Matrix.single] <;>
    native_decide

theorem reverse_transition_sum_eq_forward_conjTranspose :
    ∑ i : Fin 3, transitionMatrix (oppositeRoot (rootFromIndex i)) =
      (∑ i : Fin 3, transitionMatrix (rootFromIndex i))ᴴ := by
  rw [Matrix.conjTranspose_sum]
  apply Finset.sum_congr rfl
  intro i hi
  exact transitionMatrix_opposite_conjTranspose (rootFromIndex i)

theorem transitionMatrix_mul (r s : A2Root) :
    transitionMatrix r * transitionMatrix s =
      if r.1.2 = s.1.1 then
        Matrix.single r.1.1 s.1.2 1
      else 0 := by
  by_cases h : r.1.2 = s.1.1
  · rw [if_pos h]
    simp [transitionMatrix, Matrix.single_mul_single_same, h]
  · simp [transitionMatrix, h]

theorem transitionMatrix_mul_opposite (r : A2Root) :
    transitionMatrix r * transitionMatrix (oppositeRoot r) =
      Matrix.single r.1.1 r.1.1 1 := by
  rw [transitionMatrix_mul]
  simp [oppositeRoot]

theorem transitionMatrix_opposite_mul (r : A2Root) :
    transitionMatrix (oppositeRoot r) * transitionMatrix r =
      Matrix.single r.1.2 r.1.2 1 := by
  rw [transitionMatrix_mul]
  simp [oppositeRoot]

theorem transitionMatrix_comm_opposite (r : A2Root) :
    transitionMatrix r * transitionMatrix (oppositeRoot r) -
        transitionMatrix (oppositeRoot r) * transitionMatrix r =
      Matrix.single r.1.1 r.1.1 1 - Matrix.single r.1.2 r.1.2 1 := by
  rw [transitionMatrix_mul_opposite, transitionMatrix_opposite_mul]

theorem transitionMatrix_comm (r s : A2Root) :
    transitionMatrix r * transitionMatrix s -
        transitionMatrix s * transitionMatrix r =
      (if r.1.2 = s.1.1 then
          Matrix.single r.1.1 s.1.2 1
        else 0) -
        (if s.1.2 = r.1.1 then
          Matrix.single s.1.1 r.1.2 1
        else 0) := by
  rw [transitionMatrix_mul, transitionMatrix_mul]

theorem diagonalCartan_comm_transitionMatrix
    (h : Fin 3 → ℂ) (r : A2Root) :
    diagonalCartan h * transitionMatrix r -
        transitionMatrix r * diagonalCartan h =
      (h r.1.1 - h r.1.2) • transitionMatrix r := by
  ext i j
  simp only [diagonalCartan, transitionMatrix, Matrix.smul_apply]
  by_cases hi : i = r.1.1
  · subst i
    by_cases hj : j = r.1.2
    · subst j
      simp [Matrix.single]
    · have hj' : r.1.2 ≠ j := Ne.symm hj
      simp [Matrix.single, hj']
  · have hi' : r.1.1 ≠ i := Ne.symm hi
    by_cases hj : j = r.1.2
    · subst j
      simp [Matrix.single, hi']
    · have hj' : r.1.2 ≠ j := Ne.symm hj
      simp [Matrix.single, hi', hj']

end InfoGeometry.Canonical.A2QutritTransitionRootBridge

end noncomputable section
