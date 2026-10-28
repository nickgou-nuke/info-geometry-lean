/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.Twistor.WittenSpinorHelicity
import InfoGeometry.Canonical.PeirceBCFWKinematicBridge

/-!
# The native BCFW shift specialized to spinor momenta

The determinant polarization on native complex momentum matrices is the
pullback of the existing Peirce kinematic bilinear form. The shift vector
`lambda_j ⊗ lambdaTilde_i` supplies its null and orthogonality hypotheses.
The statements are matrix/operator kinematics, not amplitude recursion.
-/

noncomputable section

namespace InfoGeometry.Twistor.WittenSpinorBCFW

open InfoGeometry.Physics.ChiralPoincareSouriauBridge
open InfoGeometry.Twistor.PenroseIncidence
open InfoGeometry.Twistor.WittenSpinorHelicity
open InfoGeometry.Canonical

/-- The determinant ordering in the existing four Peirce coordinates. -/
def matrixChannelCoordinates : M2C →ₗ[ℂ] InfoGeometry.Algebra.FiniteSpin.Vec4C where
  toFun M := ![M 0 0, M 1 1, M 0 1, M 1 0]
  map_add' M N := by ext i; fin_cases i <;> rfl
  map_smul' c M := by ext i; fin_cases i <;> rfl

/-- Pull back the existing bilinear form along the native matrix readout. -/
def matrixMomentumPair : LinearMap.BilinForm ℂ M2C :=
  LinearMap.mk₂ ℂ
    (fun M N => peirceKinematicForm (matrixChannelCoordinates M)
      (matrixChannelCoordinates N))
    (by intro M N P; simp)
    (by intro c M N; simp)
    (by intro M N P; simp)
    (by intro c M N; simp)

theorem matrixMomentumPair_apply (M N : M2C) :
    matrixMomentumPair M N = (1 / 2 : ℂ) *
      (M 0 0 * N 1 1 + M 1 1 * N 0 0 -
        M 0 1 * N 1 0 - M 1 0 * N 0 1) := by
  simp [matrixMomentumPair, peirceKinematicForm, matrixChannelCoordinates,
    LinearMap.mk₂_apply]

theorem matrixMomentumPair_self (M : M2C) :
    matrixMomentumPair M M = M.det := by
  rw [matrixMomentumPair_apply, Matrix.det_fin_two]
  ring

theorem matrixMomentumPair_isSymm : matrixMomentumPair.IsSymm := by
  rw [LinearMap.BilinForm.isSymm_def]
  intro M N
  change peirceKinematicForm (matrixChannelCoordinates M) (matrixChannelCoordinates N) =
    peirceKinematicForm (matrixChannelCoordinates N) (matrixChannelCoordinates M)
  exact peirceKinematicForm_isSymm.eq _ _

/-- The factor one half is fixed by requiring `B(M,M) = det M`. -/
theorem matrixMomentumPair_spinorOuter
    (lambda mu lambdaTilde muTilde : Spinor2) :
    matrixMomentumPair (spinorOuter lambda lambdaTilde) (spinorOuter mu muTilde) =
      (1 / 2 : ℂ) *
        (spinorBracket lambda mu * spinorBracket lambdaTilde muTilde) := by
  rw [matrixMomentumPair_apply]
  simp only [spinorOuter, spinorBracket_apply]
  ring

/-- The actual rank-one BCFW direction. -/
def spinorShiftDirection (lambdaJ lambdaTildeI : Spinor2) : M2C :=
  spinorOuter lambdaJ lambdaTildeI

theorem spinorShiftDirection_ne_zero
    (lambdaJ lambdaTildeI : Spinor2)
    (hJ : lambdaJ ≠ 0) (hI : lambdaTildeI ≠ 0) :
    spinorShiftDirection lambdaJ lambdaTildeI ≠ 0 := by
  change spinorOuter lambdaJ lambdaTildeI ≠ 0
  exact mt (spinorOuter_eq_zero_iff lambdaJ lambdaTildeI).mp (not_or.mpr ⟨hJ, hI⟩)

theorem spinorShiftDirection_null (lambdaJ lambdaTildeI : Spinor2) :
    matrixMomentumPair (spinorShiftDirection lambdaJ lambdaTildeI)
      (spinorShiftDirection lambdaJ lambdaTildeI) = 0 := by
  rw [matrixMomentumPair_self]
  exact det_spinorOuter_zero _ _

theorem spinorShiftDirection_orthogonal_left
    (lambdaI lambdaJ lambdaTildeI : Spinor2) :
    matrixMomentumPair (spinorOuter lambdaI lambdaTildeI)
      (spinorShiftDirection lambdaJ lambdaTildeI) = 0 := by
  rw [spinorShiftDirection, matrixMomentumPair_spinorOuter, spinorBracket_self]
  ring

theorem spinorShiftDirection_orthogonal_right
    (lambdaJ lambdaTildeI lambdaTildeJ : Spinor2) :
    matrixMomentumPair (spinorOuter lambdaJ lambdaTildeJ)
      (spinorShiftDirection lambdaJ lambdaTildeI) = 0 := by
  rw [spinorShiftDirection, matrixMomentumPair_spinorOuter, spinorBracket_self]
  ring

/-- The native left shift agrees with shifting only the undotted spinor. -/
theorem shiftedPi_spinorOuter
    (lambdaI lambdaJ lambdaTildeI : Spinor2) (z : ℂ) :
    shiftedPi (spinorOuter lambdaI lambdaTildeI)
      (spinorShiftDirection lambdaJ lambdaTildeI) z =
      spinorOuter (lambdaI + z • lambdaJ) lambdaTildeI := by
  ext a b
  simp [shiftedPi, spinorShiftDirection, spinorOuter, smul_eq_mul]
  ring

/-- The native right shift agrees with shifting only the dotted spinor. -/
theorem shiftedPj_spinorOuter
    (lambdaJ lambdaTildeI lambdaTildeJ : Spinor2) (z : ℂ) :
    shiftedPj (spinorOuter lambdaJ lambdaTildeJ)
      (spinorShiftDirection lambdaJ lambdaTildeI) z =
      spinorOuter lambdaJ (lambdaTildeJ - z • lambdaTildeI) := by
  ext a b
  simp [shiftedPj, spinorShiftDirection, spinorOuter, smul_eq_mul]
  ring

/-- Left on-shell preservation consumes the existing BCFW owner theorem. -/
theorem spinor_bcfw_left_onShell
    (lambdaI lambdaJ lambdaTildeI : Spinor2) (z : ℂ) :
    (shiftedPi (spinorOuter lambdaI lambdaTildeI)
      (spinorShiftDirection lambdaJ lambdaTildeI) z).det = 0 := by
  rw [← matrixMomentumPair_self]
  exact bcfw_shift_left_null matrixMomentumPair matrixMomentumPair_isSymm _ _ z
    (by rw [matrixMomentumPair_self, det_spinorOuter_zero])
    (spinorShiftDirection_null _ _)
    (spinorShiftDirection_orthogonal_left _ _ _)

/-- Right on-shell preservation consumes the same native BCFW carrier. -/
theorem spinor_bcfw_right_onShell
    (lambdaJ lambdaTildeI lambdaTildeJ : Spinor2) (z : ℂ) :
    (shiftedPj (spinorOuter lambdaJ lambdaTildeJ)
      (spinorShiftDirection lambdaJ lambdaTildeI) z).det = 0 := by
  rw [← matrixMomentumPair_self]
  exact bcfw_shift_right_null matrixMomentumPair matrixMomentumPair_isSymm _ _ z
    (by rw [matrixMomentumPair_self, det_spinorOuter_zero])
    (spinorShiftDirection_null _ _)
    (spinorShiftDirection_orthogonal_right _ _ _)

/-- Opposite spinor shifts conserve the actual matrix sum. -/
theorem spinor_bcfw_momentum_conservation
    (lambdaI lambdaJ lambdaTildeI lambdaTildeJ : Spinor2) (z : ℂ) :
    spinorOuter (lambdaI + z • lambdaJ) lambdaTildeI +
      spinorOuter lambdaJ (lambdaTildeJ - z • lambdaTildeI) =
      spinorOuter lambdaI lambdaTildeI + spinorOuter lambdaJ lambdaTildeJ := by
  rw [← shiftedPi_spinorOuter, ← shiftedPj_spinorOuter]
  exact bcfw_shift_momentum_conservation _ _ _ z

/-- The concrete spinor direction also supplies the generic channel-pole theorem. -/
theorem spinor_bcfw_channel_onShell
    (P : M2C) (lambdaJ lambdaTildeI : Spinor2)
    (hslope : 2 * matrixMomentumPair P (spinorShiftDirection lambdaJ lambdaTildeI) ≠ 0) :
    (shiftedChannel P (spinorShiftDirection lambdaJ lambdaTildeI)
      (-P.det / (2 * matrixMomentumPair P
        (spinorShiftDirection lambdaJ lambdaTildeI)))).det = 0 := by
  rw [← matrixMomentumPair_self P, ← matrixMomentumPair_self]
  exact bcfw_channel_goes_onShell matrixMomentumPair matrixMomentumPair_isSymm P _
    (spinorShiftDirection_null _ _) hslope

end InfoGeometry.Twistor.WittenSpinorBCFW
