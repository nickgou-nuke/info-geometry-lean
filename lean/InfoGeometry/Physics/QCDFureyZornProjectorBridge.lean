import Mathlib
import InfoGeometry.Algebra.Zorn.G2TrifactorSU3

/-!
# Native Furey-style Zorn projector routing

This module promotes the finite projector/lane content of the downstream
`proofs/FureyZornFermionBridge.lean` onto the native canonical Zorn carrier.
It uses only the existing `G2TrifactorSU3` product and projectors.

Closed here:

* the two diagonal native Zorn projectors are idempotent;
* pure upper and lower `Fin 3 -> C` lanes are square-zero;
* right multiplication by the complementary projector selects the lane;
* right multiplication by the same-side projector annihilates it.

This is a finite algebraic routing theorem. It does not identify these lanes
with physical quark/lepton fields, prove an SU(3)_C gauge representation, or
prove that the Cl(5,5) Furey span is a minimal ideal.
-/

noncomputable section

namespace InfoGeometry.Physics.QCDFureyZornProjectorBridge

open InfoGeometry.Algebra.Zorn.G2TrifactorSU3

abbrev ZornC := ZMat ℂ
abbrev ColorTriplet := Fin 3 -> ℂ

/-- Upper off-diagonal native Zorn lane. -/
def upperLane (u : ColorTriplet) : ZornC :=
  { a := 0, b := 0, x := u, y := 0 }

/-- Lower off-diagonal native Zorn lane. -/
def lowerLane (v : ColorTriplet) : ZornC :=
  { a := 0, b := 0, x := 0, y := v }

/-- Right multiplication by a native diagonal projector. -/
def rightProject (P X : ZornC) : ZornC := zMul X P

/-- Pure upper lanes are square-zero for the native Zorn product. -/
theorem upperLane_sq_zero (u : ColorTriplet) :
    zMul (upperLane u) (upperLane u) = 0 := by
  apply InfoGeometry.Canonical.ZornMatrix.ext
  · change _ = (0 : ℂ)
    simp [upperLane, zMul, InfoGeometry.Canonical.ZornMatrix.dot]
  · change _ = (0 : ℂ)
    simp [upperLane, zMul, InfoGeometry.Canonical.ZornMatrix.dot]
  · funext i
    fin_cases i <;> change _ = (0 : ℂ) <;>
      simp [upperLane, zMul, InfoGeometry.Canonical.ZornMatrix.cross] <;> ring
  · funext i
    fin_cases i <;> change _ = (0 : ℂ) <;>
      simp [upperLane, zMul, InfoGeometry.Canonical.ZornMatrix.cross] <;> ring

/-- Pure lower lanes are square-zero for the native Zorn product. -/
theorem lowerLane_sq_zero (v : ColorTriplet) :
    zMul (lowerLane v) (lowerLane v) = 0 := by
  apply InfoGeometry.Canonical.ZornMatrix.ext
  · change _ = (0 : ℂ)
    simp [lowerLane, zMul, InfoGeometry.Canonical.ZornMatrix.dot]
  · change _ = (0 : ℂ)
    simp [lowerLane, zMul, InfoGeometry.Canonical.ZornMatrix.dot]
  · funext i
    fin_cases i <;> change _ = (0 : ℂ) <;>
      simp [lowerLane, zMul, InfoGeometry.Canonical.ZornMatrix.cross] <;> ring
  · funext i
    fin_cases i <;> change _ = (0 : ℂ) <;>
      simp [lowerLane, zMul, InfoGeometry.Canonical.ZornMatrix.cross] <;> ring

/-- The lower diagonal projector selects the upper lane on the right. -/
theorem upperLane_selected_by_OP2 (u : ColorTriplet) :
    rightProject (OP2 : ZornC) (upperLane u) = upperLane u := by
  ext i <;>
    simp [rightProject, upperLane, OP2, zMul,
      InfoGeometry.Canonical.ZornMatrix.dot,
      InfoGeometry.Canonical.ZornMatrix.cross]
  all_goals try { fin_cases i <;> rfl }

/-- The upper diagonal projector annihilates the upper lane on the right. -/
theorem upperLane_annihilated_by_OP1 (u : ColorTriplet) :
    rightProject (OP1 : ZornC) (upperLane u) = 0 := by
  ext i <;>
    simp [rightProject, upperLane, OP1, zMul,
      InfoGeometry.Canonical.ZornMatrix.dot,
      InfoGeometry.Canonical.ZornMatrix.cross]
  all_goals try { fin_cases i <;> rfl }
  all_goals change _ = (0 : ℂ)
  all_goals rfl

/-- The upper diagonal projector selects the lower lane on the right. -/
theorem lowerLane_selected_by_OP1 (v : ColorTriplet) :
    rightProject (OP1 : ZornC) (lowerLane v) = lowerLane v := by
  ext i <;>
    simp [rightProject, lowerLane, OP1, zMul,
      InfoGeometry.Canonical.ZornMatrix.dot,
      InfoGeometry.Canonical.ZornMatrix.cross]
  all_goals try { fin_cases i <;> rfl }

/-- The lower diagonal projector annihilates the lower lane on the right. -/
theorem lowerLane_annihilated_by_OP2 (v : ColorTriplet) :
    rightProject (OP2 : ZornC) (lowerLane v) = 0 := by
  ext i <;>
    simp [rightProject, lowerLane, OP2, zMul,
      InfoGeometry.Canonical.ZornMatrix.dot,
      InfoGeometry.Canonical.ZornMatrix.cross]
  all_goals try { fin_cases i <;> rfl }
  all_goals change _ = (0 : ℂ)
  all_goals rfl
  all_goals change _ = (0 : ℂ)
  all_goals rfl

/-- Native finite Furey/Zorn routing packet. -/
theorem furey_zorn_projector_packet :
    zMul (OP1 : ZornC) OP1 = OP1 ∧
    zMul (OP2 : ZornC) OP2 = OP2 ∧
    (∀ u : ColorTriplet, zMul (upperLane u) (upperLane u) = 0) ∧
    (∀ v : ColorTriplet, zMul (lowerLane v) (lowerLane v) = 0) ∧
    (∀ u : ColorTriplet, rightProject (OP2 : ZornC) (upperLane u) = upperLane u) ∧
    (∀ u : ColorTriplet, rightProject (OP1 : ZornC) (upperLane u) = 0) ∧
    (∀ v : ColorTriplet, rightProject (OP1 : ZornC) (lowerLane v) = lowerLane v) ∧
    (∀ v : ColorTriplet, rightProject (OP2 : ZornC) (lowerLane v) = 0) := by
  exact ⟨op1_idempotent, op2_idempotent,
    upperLane_sq_zero, lowerLane_sq_zero,
    upperLane_selected_by_OP2, upperLane_annihilated_by_OP1,
    lowerLane_selected_by_OP1, lowerLane_annihilated_by_OP2⟩

end InfoGeometry.Physics.QCDFureyZornProjectorBridge

end noncomputable section
