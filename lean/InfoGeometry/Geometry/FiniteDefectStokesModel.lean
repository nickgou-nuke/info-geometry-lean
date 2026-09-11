/-
InfoGeometry/Geometry/FiniteDefectStokesModel.lean

A finite 2x2 matrix model separating the closed-form and defect-supported
Stokes lanes.
-/

import Mathlib.Tactic
import InfoGeometry.Algebra.FiniteSpinAlgebra
import InfoGeometry.Geometry.BilingualAnalyticity
import InfoGeometry.Geometry.ConstructiveKasparov
import InfoGeometry.Geometry.SpectralDivisors

noncomputable section

namespace InfoGeometry.Geometry.FiniteDefectStokesModel

open Matrix
open InfoGeometry.Geometry.BilingualAnalyticity
open InfoGeometry.Geometry.ConstructiveKasparov
open InfoGeometry.Geometry.SpectralDivisors

abbrev Mat2 :=
  Matrix (Fin 2) (Fin 2) ℝ

/-- The finite bounded-transform piece `F = diag(1,0)`. -/
def F : Mat2 :=
  !![1, 0; 0, 0]

/-- The finite defect projector `P = diag(0,1)`. -/
def P : Mat2 :=
  !![0, 0; 0, 1]

/-- The one-point region used by the executable finite model. -/
abbrev Region := Unit

/-- The one-point space of geometric points. -/
abbrev Point := Unit

/-- The one-point tangent direction space. -/
abbrev Tangent := Unit

/-- The constant Chern form in the finite model. -/
def ccForm : OperatorOneForm Point Tangent Mat2 :=
  fun _ _ => 0

@[simp]
theorem F_apply_zero_zero :
    F 0 0 = 1 :=
  rfl

@[simp]
theorem F_apply_zero_one :
    F 0 1 = 0 :=
  rfl

@[simp]
theorem F_apply_one_zero :
    F 1 0 = 0 :=
  rfl

@[simp]
theorem F_apply_one_one :
    F 1 1 = 0 :=
  rfl

@[simp]
theorem P_apply_zero_zero :
    P 0 0 = 0 :=
  rfl

@[simp]
theorem P_apply_zero_one :
    P 0 1 = 0 :=
  rfl

@[simp]
theorem P_apply_one_zero :
    P 1 0 = 0 :=
  rfl

@[simp]
theorem P_apply_one_one :
    P 1 1 = 1 :=
  rfl

theorem F_mul_F :
    F * F = F := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [F, Matrix.mul_apply, Fin.sum_univ_two]

theorem F_mul_P :
    F * P = 0 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [F, P, Matrix.mul_apply, Fin.sum_univ_two]

theorem P_mul_F :
    P * F = 0 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [F, P, Matrix.mul_apply, Fin.sum_univ_two]

theorem P_mul_P :
    P * P = P := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [P, Matrix.mul_apply, Fin.sum_univ_two]

theorem F_add_P :
    F + P = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [F, P]

theorem P_add_F :
    P + F = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [F, P]

/-- The defect projector is the complement of the bounded transform piece. -/
theorem P_eq_one_sub_F :
    P = 1 - F := by
  have h := F_add_P
  ext i j
  have h' := congrFun (congrFun h i) j
  fin_cases i <;> fin_cases j <;> norm_num at h' ⊢

/-- The bounded transform piece is the complement of the defect projector. -/
theorem F_eq_one_sub_P :
    F = 1 - P := by
  have h := P_add_F
  ext i j
  have h' := congrFun (congrFun h i) j
  fin_cases i <;> fin_cases j <;> norm_num at h' ⊢

theorem F_mul_F_add_P :
    F * F + P = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [F, P, Matrix.mul_apply, Fin.sum_univ_two]

/-- A concrete finite bounded Dirac/Kasparov datum. -/
def boundedDirac : VerifiedBoundedDirac Mat2 where
  F := F
  P := P
  F_sq_add_P := F_mul_F_add_P
  F_P_zero := F_mul_P
  P_F_zero := P_mul_F
  P_sq := P_mul_P

/--
The finite Stokes backend with defect current `P`.

The geometric derivative is explicitly `P`, so this is the defect-supported
lane, not the closed-form lane.
-/
def defectBackend : GeometricIntegralBackend Region Point Tangent Mat2 where
  boundaryIntegral := fun _ _ => P
  volumeIntegral := fun _ f => f ()
  geometricDerivative := fun _ _ => P
  stokes_eq := by
    intro Ω ω
    rfl
  volumeIntegral_zero_of_pointwise_zero := by
    intro Ω f hf
    exact hf ()

/-- The finite Chern form has `d_geo ccForm = P`. -/
theorem geometricDerivative_ccForm_eq_defect
    (p : Point) :
    defectBackend.geometricDerivative ccForm p = boundedDirac.P :=
  rfl

/-- In the finite defect model, the boundary integral is exactly `P`. -/
theorem boundaryIntegral_ccForm :
    defectBackend.boundaryIntegral () ccForm = P :=
  rfl

/-- In the finite defect model, the volume integral of the defect is exactly `P`. -/
theorem volumeIntegral_defect :
    defectBackend.volumeIntegral () (fun _ => boundedDirac.P) = P :=
  rfl

/-- Defect-supported Stokes identity in the concrete finite model. -/
theorem boundaryIntegral_eq_volumeIntegral_defect :
    defectBackend.boundaryIntegral () ccForm =
      defectBackend.volumeIntegral () (fun _ => boundedDirac.P) :=
  defectBackend.stokes_eq () ccForm

/--
The finite model also gives a one-turn residue normalizer.  Integer multiples
of `P` are faithful because the `(1,1)` matrix entry records the integer.
-/
def defectNormalizer : PhaseResidueNormalizer Mat2 where
  phasePeriod := P
  integer_period_injective := by
    intro m n h
    have h11 :
        ((m : ℝ) • P) 1 1 = ((n : ℝ) • P) 1 1 :=
      congrFun (congrFun h 1) 1
    norm_num [P] at h11
    exact Int.cast_injective h11

/-- Certified winding datum for the one-point finite defect region. -/
def windingDatum : WindingNumberDatum defectBackend defectNormalizer ccForm where
  winding := fun _ => 1
  boundaryIntegral_eq_winding_smul := by
    intro Ω
    ext i j
    fin_cases i <;> fin_cases j <;>
      norm_num [defectBackend, defectNormalizer, P]

/-- The boundary residue is one period in the finite model. -/
theorem boundaryIntegral_eq_one_period :
    defectBackend.boundaryIntegral () ccForm =
      ((1 : ℤ) : ℝ) • defectNormalizer.phasePeriod :=
  windingDatum.boundaryIntegral_eq_winding_smul ()

/-- The finite defect volume is quantized by the certified one-turn winding. -/
theorem volumeIntegral_defect_eq_one_period :
    defectBackend.volumeIntegral () (fun _ => boundedDirac.P) =
      ((windingDatum.winding () : ℤ) : ℝ) • defectNormalizer.phasePeriod :=
  calc
    defectBackend.volumeIntegral () (fun _ => boundedDirac.P)
        = defectBackend.boundaryIntegral () ccForm := by
          rw [boundaryIntegral_eq_volumeIntegral_defect]
    _ = ((windingDatum.winding () : ℤ) : ℝ) • defectNormalizer.phasePeriod :=
          windingDatum.boundaryIntegral_eq_winding_smul ()

end InfoGeometry.Geometry.FiniteDefectStokesModel
