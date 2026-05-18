import Mathlib
import InfoGeometry.Clifford.FiniteTiltDiracShell
import InfoGeometry.OperatorAlgebra.ChiralLightconeStinespring
import InfoGeometry.OperatorAlgebra.SymmetryInvariants
import InfoGeometry.Meta.Architecture
import InfoGeometry.Meta.BridgeTarget
import InfoGeometry.Meta.OwnerTarget

/-!
# InfoGeometry.Clifford.FiniteTiltDiracShellChiralSplit

Proof-only chiral splitting of the finite tilt Dirac shell.

This file stays on the finite 2x2 matrix model already owned by
`FiniteTiltDiracShell`.  It introduces the spectral projectors of the
grading generator `tiltOddA`, proves they are complementary idempotents, and
uses them to split the shell operator into left/right chiral pieces.

No socket.
No certificate.
No CFT claim.
-/

noncomputable section

open scoped Matrix

namespace InfoGeometry.Clifford.FiniteTiltDiracShellChiralSplit

open InfoGeometry.Clifford.FiniteTiltDiracShell
open InfoGeometry.OperatorAlgebra.ChiralLightconeStinespring
open InfoGeometry.OperatorAlgebra.SymmetryInvariants

/-- The left chiral projector of the finite tilt shell. -/
@[rep_depth operator]
def finiteTiltLeftChiralProjector : Mat2 :=
  (1 / 2 : ℝ) • ((1 : Mat2) + tiltOddA)

/-- The right chiral projector of the finite tilt shell. -/
@[rep_depth operator]
def finiteTiltRightChiralProjector : Mat2 :=
  (1 / 2 : ℝ) • ((1 : Mat2) - tiltOddA)

/-- The left and right chiral projectors sum to the identity. -/
@[bridge_target_tag, rep_depth operator]
theorem finiteTiltChiralProjector_sum :
    finiteTiltLeftChiralProjector + finiteTiltRightChiralProjector = 1 := by
  ext i j <;> fin_cases i <;> fin_cases j <;>
    simp [finiteTiltLeftChiralProjector, finiteTiltRightChiralProjector,
      tiltOddA, Eplus, Matrix.one_apply, Matrix.add_apply, Matrix.smul_apply]

/-- The left chiral projector is idempotent. -/
@[bridge_target_tag, rep_depth operator]
theorem finiteTiltLeftChiralProjector_idempotent :
    finiteTiltLeftChiralProjector * finiteTiltLeftChiralProjector =
      finiteTiltLeftChiralProjector := by
  ext i j <;> fin_cases i <;> fin_cases j <;>
    simp [finiteTiltLeftChiralProjector, tiltOddA, Eplus, Matrix.mul_apply,
      Fin.sum_univ_two, Matrix.smul_apply, Matrix.add_apply] <;> ring

/-- The right chiral projector is idempotent. -/
@[bridge_target_tag, rep_depth operator]
theorem finiteTiltRightChiralProjector_idempotent :
    finiteTiltRightChiralProjector * finiteTiltRightChiralProjector =
      finiteTiltRightChiralProjector := by
  ext i j <;> fin_cases i <;> fin_cases j <;>
    simp [finiteTiltRightChiralProjector, tiltOddA, Eplus, Matrix.mul_apply,
      Fin.sum_univ_two, Matrix.smul_apply, Matrix.add_apply] <;> ring

/-- The two chiral projectors annihilate in one order. -/
@[bridge_target_tag, rep_depth operator]
theorem finiteTiltLeftRightChiralProjector_mul_zero :
    finiteTiltLeftChiralProjector * finiteTiltRightChiralProjector = 0 := by
  ext i j <;> fin_cases i <;> fin_cases j <;>
    simp [finiteTiltLeftChiralProjector, finiteTiltRightChiralProjector,
      tiltOddA, Eplus, Matrix.mul_apply, Fin.sum_univ_two, Matrix.smul_apply,
      Matrix.add_apply] <;> ring

/-- The two chiral projectors annihilate in the opposite order. -/
@[bridge_target_tag, rep_depth operator]
theorem finiteTiltRightLeftChiralProjector_mul_zero :
    finiteTiltRightChiralProjector * finiteTiltLeftChiralProjector = 0 := by
  ext i j <;> fin_cases i <;> fin_cases j <;>
    simp [finiteTiltLeftChiralProjector, finiteTiltRightChiralProjector,
      tiltOddA, Eplus, Matrix.mul_apply, Fin.sum_univ_two, Matrix.smul_apply,
      Matrix.add_apply] <;> ring

/-- The finite tilt chiral projectors form a complementary projector pair. -/
@[rep_depth operator]
def finiteTiltChiralProjectors :
    ComplementaryProjectors Mat2 where
  p := finiteTiltLeftChiralProjector
  q := finiteTiltRightChiralProjector
  p_idempotent := finiteTiltLeftChiralProjector_idempotent
  q_idempotent := finiteTiltRightChiralProjector_idempotent
  sum_eq_one := finiteTiltChiralProjector_sum
  pq_zero := finiteTiltLeftRightChiralProjector_mul_zero
  qp_zero := finiteTiltRightLeftChiralProjector_mul_zero

/-- The finite tilt shell chiral projectors as a chiral projector pair. -/
@[rep_depth operator]
def finiteTiltChiralProjectorPair : ChiralProjectorPair Mat2 where
  PL := finiteTiltLeftChiralProjector
  PR := finiteTiltRightChiralProjector
  PL_idem := finiteTiltLeftChiralProjector_idempotent
  PR_idem := finiteTiltRightChiralProjector_idempotent
  complementary := finiteTiltChiralProjector_sum
  disjoint_left := finiteTiltLeftRightChiralProjector_mul_zero
  disjoint_right := finiteTiltRightLeftChiralProjector_mul_zero

/-- The left chiral shell component. -/
@[rep_depth operator]
def finiteTiltLeftChiralShell (m : ℝ) : Mat2 :=
  finiteTiltChiralProjectors.pComponent (finiteTiltDiracShell m)

/-- The right chiral shell component. -/
@[rep_depth operator]
def finiteTiltRightChiralShell (m : ℝ) : Mat2 :=
  finiteTiltChiralProjectors.qComponent (finiteTiltDiracShell m)

/-- The finite shell splits into left and right chiral components. -/
@[bridge_target_tag, rep_depth operator]
theorem finiteTiltDiracShell_chiral_decomposition (m : ℝ) :
    finiteTiltLeftChiralShell m + finiteTiltRightChiralShell m =
      finiteTiltDiracShell m := by
  simpa [finiteTiltLeftChiralShell, finiteTiltRightChiralShell] using
      ComplementaryProjectors.left_decomposition
      finiteTiltChiralProjectors (finiteTiltDiracShell m)

/-- The finite shell splits through the explicit chiral projector pair. -/
@[bridge_target_tag, rep_depth operator]
theorem finiteTiltDiracShell_chiral_pair_decomposition (m : ℝ) :
    finiteTiltChiralProjectorPair.PL * finiteTiltDiracShell m +
      finiteTiltChiralProjectorPair.PR * finiteTiltDiracShell m =
        finiteTiltDiracShell m := by
  simpa [finiteTiltChiralProjectorPair] using
    ComplementaryProjectors.left_decomposition
      finiteTiltChiralProjectors (finiteTiltDiracShell m)

/-- The left chiral component is supported on the left projector. -/
@[bridge_target_tag, rep_depth operator]
theorem finiteTiltLeftChiralShell_supported (m : ℝ) :
    IsSupportedOn finiteTiltChiralProjectors.p (finiteTiltLeftChiralShell m) := by
  simpa [finiteTiltLeftChiralShell] using
      ComplementaryProjectors.pComponent_supported
      finiteTiltChiralProjectors (finiteTiltDiracShell m)

/-- The left chiral component is supported on the explicit chiral projector. -/
@[bridge_target_tag, rep_depth operator]
theorem finiteTiltLeftChiralShell_supported_by_pair (m : ℝ) :
    finiteTiltChiralProjectorPair.IsLeftSupported (finiteTiltLeftChiralShell m) := by
  simpa [finiteTiltChiralProjectorPair, finiteTiltLeftChiralShell] using
    finiteTiltLeftChiralShell_supported (m := m)

/-- The right chiral component is supported on the right projector. -/
@[bridge_target_tag, rep_depth operator]
theorem finiteTiltRightChiralShell_supported (m : ℝ) :
    IsSupportedOn finiteTiltChiralProjectors.q (finiteTiltRightChiralShell m) := by
  simpa [finiteTiltRightChiralShell] using
      ComplementaryProjectors.qComponent_supported
      finiteTiltChiralProjectors (finiteTiltDiracShell m)

/-- The right chiral component is supported on the explicit chiral projector. -/
@[bridge_target_tag, rep_depth operator]
theorem finiteTiltRightChiralShell_supported_by_pair (m : ℝ) :
    finiteTiltChiralProjectorPair.IsRightSupported (finiteTiltRightChiralShell m) := by
  simpa [finiteTiltChiralProjectorPair, finiteTiltRightChiralShell] using
    finiteTiltRightChiralShell_supported (m := m)

/-- The left projector fixes the left chiral shell component. -/
@[bridge_target_tag, rep_depth operator]
theorem finiteTiltLeftChiralProjector_mul_leftChiralShell (m : ℝ) :
    finiteTiltChiralProjectors.p * finiteTiltLeftChiralShell m =
      finiteTiltLeftChiralShell m :=
  finiteTiltLeftChiralShell_supported m

/-- The right projector kills the left chiral shell component. -/
@[bridge_target_tag, rep_depth operator]
theorem finiteTiltRightChiralProjector_mul_leftChiralShell (m : ℝ) :
    finiteTiltChiralProjectors.q * finiteTiltLeftChiralShell m = 0 := by
  calc
    finiteTiltChiralProjectors.q * finiteTiltLeftChiralShell m
        = finiteTiltChiralProjectors.q *
            (finiteTiltChiralProjectors.p * finiteTiltLeftChiralShell m) := by
              rw [finiteTiltLeftChiralShell_supported m]
    _ = (finiteTiltChiralProjectors.q * finiteTiltChiralProjectors.p) *
          finiteTiltLeftChiralShell m := by
          rw [mul_assoc]
    _ = 0 := by
          rw [finiteTiltChiralProjectors.qp_zero, zero_mul]

/-- The right projector fixes the right chiral shell component. -/
@[bridge_target_tag, rep_depth operator]
theorem finiteTiltRightChiralProjector_mul_rightChiralShell (m : ℝ) :
    finiteTiltChiralProjectors.q * finiteTiltRightChiralShell m =
      finiteTiltRightChiralShell m :=
  finiteTiltRightChiralShell_supported m

/-- The left projector kills the right chiral shell component. -/
@[bridge_target_tag, rep_depth operator]
theorem finiteTiltLeftChiralProjector_mul_rightChiralShell (m : ℝ) :
    finiteTiltChiralProjectors.p * finiteTiltRightChiralShell m = 0 := by
  calc
    finiteTiltChiralProjectors.p * finiteTiltRightChiralShell m
        = finiteTiltChiralProjectors.p *
            (finiteTiltChiralProjectors.q * finiteTiltRightChiralShell m) := by
              rw [finiteTiltRightChiralShell_supported m]
    _ = (finiteTiltChiralProjectors.p * finiteTiltChiralProjectors.q) *
          finiteTiltRightChiralShell m := by
          rw [mul_assoc]
    _ = 0 := by
          rw [finiteTiltChiralProjectors.pq_zero, zero_mul]

/-- Owner target for the finite tilt shell chiral split. -/
@[owner_target_tag]
def FiniteTiltDiracShellChiralSplitOwnerTarget : Prop :=
  ∀ m : ℝ,
    finiteTiltLeftChiralShell m + finiteTiltRightChiralShell m =
      finiteTiltDiracShell m ∧
    IsSupportedOn finiteTiltChiralProjectors.p (finiteTiltLeftChiralShell m) ∧
    IsSupportedOn finiteTiltChiralProjectors.q (finiteTiltRightChiralShell m)

/-- The finite tilt shell chiral split owner target is closed. -/
theorem finiteTiltDiracShellChiralSplitOwnerTarget :
    FiniteTiltDiracShellChiralSplitOwnerTarget := by
  intro m
  exact ⟨finiteTiltDiracShell_chiral_decomposition m,
    finiteTiltLeftChiralShell_supported m,
    finiteTiltRightChiralShell_supported m⟩

end InfoGeometry.Clifford.FiniteTiltDiracShellChiralSplit
