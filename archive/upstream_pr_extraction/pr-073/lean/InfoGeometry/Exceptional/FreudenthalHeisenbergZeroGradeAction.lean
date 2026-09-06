import InfoGeometry.Exceptional.FreudenthalSymplecticAction

/-!
# Zero-grade symplectic action on the Freudenthal Heisenberg sector

This file records the part of the five-grade action that is already forced by
the native symplectic carrier.  A symplectic infinitesimal operator acts on the
charge coordinate and trivially on the central coordinate; its derivation law
for the Heisenberg bracket is exactly the defining symplectic identity.

No identification of the zero-grade carrier with `𝔢₇` is made here.
-/

noncomputable section

namespace InfoGeometry.Exceptional.Freudenthal

variable {J : Type*} [AddCommGroup J] [Module ℝ J]
variable (D : CubicJordanDatum J)

/-- The charge action of a zero-grade endomorphism on the Heisenberg carrier.
The central grade-two coordinate is fixed infinitesimally. -/
def zeroGradeHeisenbergAction
    (T : Module.End ℝ (FreudenthalCharge J))
    (X : HeisenbergElement J) : HeisenbergElement J where
  charge := T X.charge
  center := 0

@[simp] theorem zeroGradeHeisenbergAction_charge
    (T : Module.End ℝ (FreudenthalCharge J)) (X : HeisenbergElement J) :
    (zeroGradeHeisenbergAction T X).charge = T X.charge := rfl

@[simp] theorem zeroGradeHeisenbergAction_center
    (T : Module.End ℝ (FreudenthalCharge J)) (X : HeisenbergElement J) :
    (zeroGradeHeisenbergAction T X).center = 0 := rfl

/-- A symplectic zero-grade operator differentiates the Heisenberg bracket. -/
theorem zeroGradeHeisenbergAction_bracket
    (T : Module.End ℝ (FreudenthalCharge J))
    (hT : IsSymplecticOperator D T)
    (X Y : HeisenbergElement J) :
    (HeisenbergElement.bracket D
        (zeroGradeHeisenbergAction T X) Y).center +
      (HeisenbergElement.bracket D X
        (zeroGradeHeisenbergAction T Y)).center = 0 := by
  simp only [HeisenbergElement.bracket_center,
    zeroGradeHeisenbergAction_charge]
  exact hT X.charge Y.charge

/-- The zero-grade symplectic action is a derivation of the additive
Heisenberg bracket carrier. -/
theorem zeroGradeHeisenbergAction_derivation
    (T : Module.End ℝ (FreudenthalCharge J))
    (hT : IsSymplecticOperator D T)
    (X Y : HeisenbergElement J) :
    zeroGradeHeisenbergAction T (HeisenbergElement.bracket D X Y) =
      HeisenbergElement.bracket D (zeroGradeHeisenbergAction T X) Y +
        HeisenbergElement.bracket D X (zeroGradeHeisenbergAction T Y) := by
  have hz : HeisenbergElement.zeroCharge =
      (0 : FreudenthalCharge J) := by
    apply FreudenthalCharge.ext <;> rfl
  apply HeisenbergElement.ext
  · apply FreudenthalCharge.ext
    · simp [zeroGradeHeisenbergAction, hz]
    · simp [zeroGradeHeisenbergAction, hz]
    · simp [zeroGradeHeisenbergAction, hz]
    · simp [zeroGradeHeisenbergAction, hz]
  · simp only [HeisenbergElement.bracket_center,
      zeroGradeHeisenbergAction_charge, heisenberg_center_add]
    exact (hT X.charge Y.charge).symm

@[simp] theorem zeroGradeHeisenbergAction_bracket_center
    (T : Module.End ℝ (FreudenthalCharge J))
    (X Y : HeisenbergElement J) :
    (zeroGradeHeisenbergAction T
    (HeisenbergElement.bracket D X Y)).center = 0 := rfl

/-! The charge action also reflects the commutator of zero-grade
operators.  This is the concrete closure statement available before any
identification of the symplectic carrier with `𝔢₇`. -/

theorem zeroGradeHeisenbergAction_commutator
    (T U : Module.End ℝ (FreudenthalCharge J))
    (X : HeisenbergElement J) :
    zeroGradeHeisenbergAction ⁅T, U⁆ X =
      zeroGradeHeisenbergAction T
          (zeroGradeHeisenbergAction U X) -
        zeroGradeHeisenbergAction U
          (zeroGradeHeisenbergAction T X) := by
  apply HeisenbergElement.ext
  · apply FreudenthalCharge.ext <;>
      rfl
  · change (0 : ℝ) = 0 - 0
    ring

theorem zeroGradeHeisenbergAction_add
    (T : Module.End ℝ (FreudenthalCharge J))
    (X Y : HeisenbergElement J) :
    zeroGradeHeisenbergAction T (X + Y) =
      zeroGradeHeisenbergAction T X + zeroGradeHeisenbergAction T Y := by
  apply HeisenbergElement.ext
  · change T (X.charge + Y.charge) = T X.charge + T Y.charge
    exact T.map_add X.charge Y.charge
  · change (0 : ℝ) = 0 + 0
    ring

theorem zeroGradeHeisenbergAction_smul
    (T : Module.End ℝ (FreudenthalCharge J))
    (r : ℝ) (X : HeisenbergElement J) :
    zeroGradeHeisenbergAction T (r • X) =
      r • zeroGradeHeisenbergAction T X := by
  apply HeisenbergElement.ext
  · change T (r • X.charge) = r • T X.charge
    exact T.map_smul r X.charge
  · change (0 : ℝ) = r • 0
    simp

end InfoGeometry.Exceptional.Freudenthal
