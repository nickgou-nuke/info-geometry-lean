/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import Mathlib.Algebra.Lie.OfAssociative
import InfoGeometry.Physics.NuclearDecayInference
import InfoGeometry.Physics.NuclearFiveGradeSolovievCommonCompression

/-!
# Configuration operators in the existing five-graded CAR--phonon carrier

The split linear embedding gives a faithful multiplicative corner lift.
Its unit is the model projector. Completing a finite basis change by the
identity on the complementary kernel gives full-carrier invertible operators.
All five adjoint grades survive conjugation by these completed rotations.
The model matrix readout has no implicit Hilbert-space or Born-rule meaning.
-/

noncomputable section

namespace InfoGeometry.Physics.NuclearConfigurationOperatorLift

open Matrix
open InfoGeometry.Physics.NuclearFiveGradeCommonCarrierRepresentation
open InfoGeometry.Physics.NuclearFiveGradeSolovievCommonCompression
open InfoGeometry.Physics.NuclearTwoModeFiveGradeLieModel
open InfoGeometry.Physics.NuclearConfigurationMixing
open InfoGeometry.Physics.SolovievTransitionStrength
open InfoGeometry.Physics.SolovievQPNMEigenproblem
open InfoGeometry.Topology.KatzSarnakRandomMatrixBridge

local notation "M2" => InfoGeometry.Algebra.FiniteSpin.Mat2R
local notation "G" => representation gradingOperator

local instance : LieRing M2 := LieRing.ofAssociativeRing
local instance : LieRing Operator := LieRing.ofAssociativeRing

/-- Lift into the model corner of the existing common endomorphism algebra. -/
def cornerLift : M2 →ₗ[ℝ] Operator where
  toFun O := modelEmbed.comp ((Matrix.toLin' O).comp modelReadout)
  map_add' O Q := by
    apply LinearMap.ext
    intro ψ
    simp only [map_add, LinearMap.add_comp, LinearMap.comp_add, LinearMap.comp_apply,
      LinearMap.add_apply]
  map_smul' a O := by
    apply LinearMap.ext
    intro ψ
    simp only [map_smul, LinearMap.smul_comp, LinearMap.comp_smul, LinearMap.comp_apply,
      LinearMap.smul_apply, RingHom.id_apply]

@[simp] theorem cornerLift_apply (O : M2) (ψ : Carrier) :
    cornerLift O ψ = modelEmbed (O.mulVec (modelReadout ψ)) := rfl

@[simp] theorem cornerLift_modelEmbed (O : M2) (v : ModelVector) :
    cornerLift O (modelEmbed v) = modelEmbed (O.mulVec v) := by
  simp

theorem cornerLift_mul (O Q : M2) :
    cornerLift (O * Q) = cornerLift O * cornerLift Q := by
  apply LinearMap.ext
  intro ψ
  simp only [Module.End.mul_apply, cornerLift_apply, modelReadout_modelEmbed,
    Matrix.mulVec_mulVec]

@[simp] theorem cornerLift_one : cornerLift (1 : M2) = modelProjection := by
  apply LinearMap.ext
  intro ψ
  simp [modelProjection]

/-- Compression is a readout, not an algebra homomorphism on arbitrary operators. -/
def modelMatrix (T : Operator) : M2 :=
  LinearMap.toMatrix' (modelReadout.comp (T.comp modelEmbed))

@[simp] theorem modelMatrix_mulVec (T : Operator) (v : ModelVector) :
    (modelMatrix T).mulVec v = modelReadout (T (modelEmbed v)) := by
  simp [modelMatrix]

@[simp] theorem modelMatrix_cornerLift (O : M2) : modelMatrix (cornerLift O) = O := by
  apply Matrix.toLin'.injective
  apply LinearMap.ext
  intro v
  change (modelMatrix (cornerLift O)).mulVec v = O.mulVec v
  rw [modelMatrix_mulVec, cornerLift_modelEmbed, modelReadout_modelEmbed]

theorem cornerLift_injective : Function.Injective cornerLift := by
  intro O Q h
  simpa using congrArg modelMatrix h

/-- A native faithful Lie representation; its associative unit maps to `P`. -/
def cornerLieHom : M2 →ₗ⁅ℝ⁆ Operator where
  toLinearMap := cornerLift
  map_lie' := by
    intro O Q
    change cornerLift (O * Q - Q * O) = _
    rw [map_sub, cornerLift_mul, cornerLift_mul]
    rfl

theorem projection_mul_cornerLift (O : M2) :
    modelProjection * cornerLift O = cornerLift O := by
  rw [← cornerLift_one, ← cornerLift_mul, one_mul]

theorem cornerLift_mul_projection (O : M2) :
    cornerLift O * modelProjection = cornerLift O := by
  rw [← cornerLift_one, ← cornerLift_mul, mul_one]

/-- The selected fixed-fermion model vectors have centered occupation zero. -/
theorem grading_modelEmbed (v : ModelVector) : G (modelEmbed v) = 0 := by
  rw [gradingOperator_eq_diagonal]
  funext n i
  fin_cases i <;> cases n with
  | zero => simp [representation_apply, Fin.sum_univ_four, modelEmbed,
      quasiparticleKet, InfoGeometry.Algebra.ZornVectorMatrix.zero_smul]
  | succ n =>
      cases n <;> simp [representation_apply, Fin.sum_univ_four, modelEmbed,
        quasiparticleKet, InfoGeometry.Algebra.ZornVectorMatrix.zero_smul]
      all_goals exact nsmul_zero 4

theorem modelReadout_grading (ψ : Carrier) : modelReadout (G ψ) = 0 := by
  rw [gradingOperator_eq_diagonal]
  ext i
  fin_cases i <;> simp [modelReadout, representation_apply, Fin.sum_univ_four,
    InfoGeometry.Algebra.ZornVectorMatrix.zero_smul]

theorem grading_mul_cornerLift (O : M2) : G * cornerLift O = 0 := by
  apply LinearMap.ext
  intro ψ
  simp [Module.End.mul_apply, grading_modelEmbed]

theorem cornerLift_mul_grading (O : M2) : cornerLift O * G = 0 := by
  apply LinearMap.ext
  intro ψ
  simp [Module.End.mul_apply, modelReadout_grading]

/-- Every lifted configuration operator belongs to the existing zero grade. -/
theorem cornerLift_grade_zero (O : M2) : RepresentedHasGrade 0 (cornerLift O) := by
  simp [RepresentedHasGrade, grading_mul_cornerLift, cornerLift_mul_grading]

/-- A nonzero adjoint grade has no matrix element inside this grade-zero corner. -/
theorem modelMatrix_eq_zero_of_nonzero_grade (T : Operator) (k : ℤ)
    (hk : k ≠ 0) (hT : RepresentedHasGrade k T) : modelMatrix T = 0 := by
  have hkR : (k : ℝ) ≠ 0 := by exact_mod_cast hk
  apply Matrix.toLin'.injective
  apply LinearMap.ext
  intro v
  funext i
  have h := congrArg (fun S : Operator => modelReadout (S (modelEmbed v))) hT
  simp only [LinearMap.sub_apply, Module.End.mul_apply, grading_modelEmbed,
    map_zero, modelReadout_grading, sub_zero, LinearMap.smul_apply,
    map_smul] at h
  have hi := congrFun h i
  simp only [Pi.zero_apply, Pi.smul_apply, smul_eq_mul] at hi
  have hv : modelReadout (T (modelEmbed v)) i = 0 :=
    (mul_eq_zero.mp hi.symm).resolve_left hkR
  change (modelMatrix T).mulVec v i = (0 : M2).mulVec v i
  simpa only [modelMatrix_mulVec, Matrix.zero_mulVec, Pi.zero_apply] using hv

/-- Extend an operator by the identity off the model corner. This is
multiplicative, but is not a linear map. -/
def completedLift (O : M2) : Operator := 1 - modelProjection + cornerLift O

@[simp] theorem completedLift_one : completedLift (1 : M2) = 1 := by
  simp [completedLift]

theorem completedLift_mul (O Q : M2) :
    completedLift O * completedLift Q = completedLift (O * Q) := by
  simp only [completedLift, add_mul, mul_add, sub_mul, mul_sub, one_mul, mul_one,
    modelProjection_idempotent, projection_mul_cornerLift, cornerLift_mul_projection,
    ← cornerLift_mul]
  abel

theorem completedLift_modelEmbed (O : M2) (v : ModelVector) :
    completedLift O (modelEmbed v) = modelEmbed (O.mulVec v) := by
  simp [completedLift]

theorem grading_commutes_completedLift (O : M2) :
    G * completedLift O = completedLift O * G := by
  have hGP : G * modelProjection = 0 := by
    rw [← cornerLift_one]; exact grading_mul_cornerLift 1
  have hPG : modelProjection * G = 0 := by
    rw [← cornerLift_one]; exact cornerLift_mul_grading 1
  simp [completedLift, mul_add, add_mul, mul_sub, sub_mul, hGP, hPG,
    grading_mul_cornerLift, cornerLift_mul_grading]

/-- The normalized mixing rotation has an explicit full-carrier inverse. -/
theorem completed_rotation_inverse (c s : ℝ) (h : c ^ 2 + s ^ 2 = 1) :
    completedLift (rotationMatrix c s) * completedLift (rotationMatrix c s)ᵀ = 1 ∧
    completedLift (rotationMatrix c s)ᵀ * completedLift (rotationMatrix c s) = 1 := by
  constructor
  · rw [completedLift_mul, rotationMatrix_mul_transpose_of_unit_circle h, completedLift_one]
  · rw [completedLift_mul, rotationMatrix_transpose_mul_self h, completedLift_one]

/-- Conjugating by the completed rotation preserves every adjoint grade.
Normalization is needed for invertibility, not for this intertwining identity. -/
theorem completed_rotation_preserves_grade (c s : ℝ) (T : Operator) (k : ℤ)
    (hT : RepresentedHasGrade k T) :
    RepresentedHasGrade k
      (completedLift (rotationMatrix c s) * T * completedLift (rotationMatrix c s)ᵀ) := by
  unfold RepresentedHasGrade at hT ⊢
  let U := completedLift (rotationMatrix c s)
  let V := completedLift (rotationMatrix c s)ᵀ
  have hU : G * U = U * G := grading_commutes_completedLift _
  have hV : G * V = V * G := grading_commutes_completedLift _
  change G * (U * T * V) - (U * T * V) * G = (k : ℝ) • (U * T * V)
  calc
    _ = U * (G * T - T * G) * V := by
      simp only [mul_sub, sub_mul]
      have hleft : G * (U * T * V) = U * (G * T) * V := by
        calc
          _ = (G * U) * T * V := by noncomm_ring
          _ = (U * G) * T * V := by rw [hU]
          _ = _ := by noncomm_ring
      have hright : (U * T * V) * G = U * (T * G) * V := by
        calc
          _ = U * T * (V * G) := by noncomm_ring
          _ = U * T * (G * V) := by rw [← hV]
          _ = _ := by noncomm_ring
      rw [hleft, hright]
    _ = _ := by rw [hT]; simp [mul_assoc]

end InfoGeometry.Physics.NuclearConfigurationOperatorLift
