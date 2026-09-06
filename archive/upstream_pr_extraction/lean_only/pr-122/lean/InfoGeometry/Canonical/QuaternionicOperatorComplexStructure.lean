/-
InfoGeometry/Canonical/QuaternionicOperatorComplexStructure.lean

Operator-level completion of the quaternion/Pauli/chiral cone corridor.

The repository already owns:
* the Pauli soldering map and its determinant/Casimir readout;
* the circular (raising/lowering) basis;
* the Dirac-Pauli gamma matrices and their spatial bivectors;
* the Hodge-star complex structure and chiral projectors.

This file does not create a second Clifford or braid carrier.  It packages the
existing matrix identities as an operator frame, transports the frame to
real-linear spinor endomorphisms, and records the finite Hermitian/skew and
determinant-square-root readouts.  The square-root statement is algebraic and
finite-dimensional; no unbounded Laplace-Beltrami operator is introduced.
-/

import Mathlib.Tactic
import Mathlib.LinearAlgebra.Matrix.Notation
import InfoGeometry.Clifford.DiracPauliGamma
import InfoGeometry.Clifford.QuaternionPauliRealForm
import InfoGeometry.Canonical.QuaternionEmbedding
import InfoGeometry.Canonical.HodgeStar4D
import InfoGeometry.Canonical.PauliHestenesSpinMomentum
import InfoGeometry.Canonical.RealMirrorComplexStructure
import InfoGeometry.Quantum.CircularPauliCausalCone

noncomputable section

namespace InfoGeometry.Canonical.QuaternionicOperatorComplexStructure

open Matrix
open InfoGeometry.Clifford.DiracPauliGamma
open InfoGeometry.Canonical.PauliHestenesSpinMomentum
open InfoGeometry.Quantum.PauliSoldering
open InfoGeometry.Quantum.CircularPauliCausalCone

/-! ## Quaternionic operator frames -/

/-- A quaternionic frame inside an associative operator algebra.

The three displayed generators are not required to be central.  This is
deliberately different from the central square-root interface in
EmergentComplexStructure: each unit is instead lifted to a complex structure
on a module by left action. -/
structure QuaternionicOperatorFrame (A : Type*) [Ring A] where
  i : A
  j : A
  k : A
  i_sq : i * i = -(1 : A)
  j_sq : j * j = -(1 : A)
  k_sq : k * k = -(1 : A)
  ij : i * j = k
  jk : j * k = i
  ki : k * i = j

namespace QuaternionicOperatorFrame

variable {A : Type*} [Ring A]
variable (Q : QuaternionicOperatorFrame A)

/-- The reversed products are forced by associativity and the oriented
quaternion multiplication table. -/
theorem j_mul_i : Q.j * Q.i = -Q.k := by
  calc
    Q.j * Q.i = (Q.k * Q.i) * Q.i := by rw [Q.ki]
    _ = Q.k * (Q.i * Q.i) := by rw [mul_assoc]
    _ = Q.k * (-(1 : A)) := by rw [Q.i_sq]
    _ = -Q.k := by simp

theorem k_mul_j : Q.k * Q.j = -Q.i := by
  calc
    Q.k * Q.j = (Q.i * Q.j) * Q.j := by rw [Q.ij]
    _ = Q.i * (Q.j * Q.j) := by rw [mul_assoc]
    _ = Q.i * (-(1 : A)) := by rw [Q.j_sq]
    _ = -Q.i := by simp

theorem i_mul_k : Q.i * Q.k = -Q.j := by
  calc
    Q.i * Q.k = (Q.j * Q.k) * Q.k := by rw [Q.jk]
    _ = Q.j * (Q.k * Q.k) := by rw [mul_assoc]
    _ = Q.j * (-(1 : A)) := by rw [Q.k_sq]
    _ = -Q.j := by simp

end QuaternionicOperatorFrame

/-- Existing Dirac bivectors as one quaternionic operator frame. -/
def diracQuaternionicOperatorFrame :
    QuaternionicOperatorFrame DiracMatrix where
  i := InfoGeometry.Canonical.QuaternionEmbedding.quat_i
  j := InfoGeometry.Canonical.QuaternionEmbedding.quat_j
  k := InfoGeometry.Canonical.QuaternionEmbedding.quat_k
  i_sq := InfoGeometry.Canonical.QuaternionEmbedding.quat_i_sq
  j_sq := InfoGeometry.Canonical.QuaternionEmbedding.quat_j_sq
  k_sq := InfoGeometry.Canonical.QuaternionEmbedding.quat_k_sq
  ij := InfoGeometry.Canonical.QuaternionEmbedding.quat_ij_eq_k
  jk := InfoGeometry.Canonical.QuaternionEmbedding.quat_jk_eq_i
  ki := InfoGeometry.Canonical.QuaternionEmbedding.quat_ki_eq_j

/-- Existing two-by-two Pauli realization of the same quaternionic frame. -/
def pauliQuaternionicOperatorFrame :
    QuaternionicOperatorFrame
      InfoGeometry.Clifford.QuaternionPauliRealForm.Mat2C where
  i := InfoGeometry.Clifford.QuaternionPauliRealForm.qi
  j := InfoGeometry.Clifford.QuaternionPauliRealForm.qj
  k := InfoGeometry.Clifford.QuaternionPauliRealForm.qk
  i_sq := InfoGeometry.Clifford.QuaternionPauliRealForm.qi_sq
  j_sq := InfoGeometry.Clifford.QuaternionPauliRealForm.qj_sq
  k_sq := InfoGeometry.Clifford.QuaternionPauliRealForm.qk_sq
  ij := InfoGeometry.Clifford.QuaternionPauliRealForm.qi_mul_qj
  jk := InfoGeometry.Clifford.QuaternionPauliRealForm.qj_mul_qk
  ki := InfoGeometry.Clifford.QuaternionPauliRealForm.qk_mul_qi

/-- The native two-dimensional Pauli column carrier. -/
abbrev PauliMatrix :=
  InfoGeometry.Clifford.QuaternionPauliRealForm.Mat2C
abbrev PauliSpinor := Fin 2 → ℂ
abbrev PauliSpinorOperator := PauliSpinor →ₗ[ℂ] PauliSpinor

/-- The left action of a two-by-two Pauli matrix on its column carrier. -/
noncomputable def pauliSpinorAction (A : PauliMatrix) : PauliSpinorOperator :=
  Matrix.toLin' A

theorem pauliSpinorAction_mul (A B : PauliMatrix) :
    (pauliSpinorAction A).comp (pauliSpinorAction B) =
      pauliSpinorAction (A * B) := by
  change (Matrix.toLin' A).comp (Matrix.toLin' B) =
    Matrix.toLin' (A * B)
  rw [← Matrix.toLin'_mul]

theorem pauliSpinorAction_sq_of (A : PauliMatrix)
    (hA : A * A = -(1 : PauliMatrix)) :
    (pauliSpinorAction A).comp (pauliSpinorAction A) =
      -(LinearMap.id : PauliSpinorOperator) := by
  have hcomp :
      (Matrix.toLin' A).comp (Matrix.toLin' A) =
        Matrix.toLin' (-(1 : PauliMatrix)) := by
    rw [← Matrix.toLin'_mul, hA]
  simpa [pauliSpinorAction] using hcomp

noncomputable def pauliComplexI : PauliSpinorOperator :=
  pauliSpinorAction InfoGeometry.Clifford.QuaternionPauliRealForm.qi

noncomputable def pauliComplexJ : PauliSpinorOperator :=
  pauliSpinorAction InfoGeometry.Clifford.QuaternionPauliRealForm.qj

noncomputable def pauliComplexK : PauliSpinorOperator :=
  pauliSpinorAction InfoGeometry.Clifford.QuaternionPauliRealForm.qk

theorem pauliComplexI_sq :
    pauliComplexI.comp pauliComplexI =
      -(LinearMap.id : PauliSpinorOperator) := by
  simpa [pauliComplexI] using
    (pauliSpinorAction_sq_of
      InfoGeometry.Clifford.QuaternionPauliRealForm.qi
      InfoGeometry.Clifford.QuaternionPauliRealForm.qi_sq)

theorem pauliComplexJ_sq :
    pauliComplexJ.comp pauliComplexJ =
      -(LinearMap.id : PauliSpinorOperator) := by
  simpa [pauliComplexJ] using
    (pauliSpinorAction_sq_of
      InfoGeometry.Clifford.QuaternionPauliRealForm.qj
      InfoGeometry.Clifford.QuaternionPauliRealForm.qj_sq)

theorem pauliComplexK_sq :
    pauliComplexK.comp pauliComplexK =
      -(LinearMap.id : PauliSpinorOperator) := by
  simpa [pauliComplexK] using
    (pauliSpinorAction_sq_of
      InfoGeometry.Clifford.QuaternionPauliRealForm.qk
      InfoGeometry.Clifford.QuaternionPauliRealForm.qk_sq)

theorem pauliComplexI_comp_J :
    pauliComplexI.comp pauliComplexJ = pauliComplexK := by
  calc
    pauliComplexI.comp pauliComplexJ =
        pauliSpinorAction
          (InfoGeometry.Clifford.QuaternionPauliRealForm.qi *
            InfoGeometry.Clifford.QuaternionPauliRealForm.qj) :=
      pauliSpinorAction_mul _ _
    _ = pauliComplexK := by
      rw [InfoGeometry.Clifford.QuaternionPauliRealForm.qi_mul_qj]

theorem pauliComplexJ_comp_K :
    pauliComplexJ.comp pauliComplexK = pauliComplexI := by
  calc
    pauliComplexJ.comp pauliComplexK =
        pauliSpinorAction
          (InfoGeometry.Clifford.QuaternionPauliRealForm.qj *
            InfoGeometry.Clifford.QuaternionPauliRealForm.qk) :=
      pauliSpinorAction_mul _ _
    _ = pauliComplexI := by
      rw [InfoGeometry.Clifford.QuaternionPauliRealForm.qj_mul_qk]

theorem pauliComplexK_comp_I :
    pauliComplexK.comp pauliComplexI = pauliComplexJ := by
  calc
    pauliComplexK.comp pauliComplexI =
        pauliSpinorAction
          (InfoGeometry.Clifford.QuaternionPauliRealForm.qk *
            InfoGeometry.Clifford.QuaternionPauliRealForm.qi) :=
      pauliSpinorAction_mul _ _
    _ = pauliComplexJ := by
      rw [InfoGeometry.Clifford.QuaternionPauliRealForm.qk_mul_qi]

/-! ## Lifting matrix operators to spinor endomorphisms -/

abbrev SpinorCarrier := DiracSpinor
abbrev SpinorOperator := SpinorCarrier →ₗ[ℂ] SpinorCarrier
abbrev RealSpinorOperator := SpinorCarrier →ₗ[ℝ] SpinorCarrier

/-- The left action of a finite Dirac matrix on the existing spinor carrier. -/
noncomputable def spinorAction (A : DiracMatrix) : SpinorOperator :=
  Matrix.toLin' A

/-- Matrix multiplication is transported to composition of spinor actions. -/
theorem spinorAction_mul (A B : DiracMatrix) :
    (spinorAction A).comp (spinorAction B) =
      spinorAction (A * B) := by
  change (Matrix.toLin' A).comp (Matrix.toLin' B) =
    Matrix.toLin' (A * B)
  rw [← Matrix.toLin'_mul]

/-- A square-minus-one matrix operator gives a square-minus-one complex
spinor endomorphism. -/
theorem spinorAction_sq_of (A : DiracMatrix)
    (hA : A * A = -(1 : DiracMatrix)) :
    (spinorAction A).comp (spinorAction A) =
      -(LinearMap.id : SpinorOperator) := by
  have hcomp :
      (Matrix.toLin' A).comp (Matrix.toLin' A) =
        Matrix.toLin' (-(1 : DiracMatrix)) := by
    rw [← Matrix.toLin'_mul, hA]
  simpa [spinorAction] using hcomp

/-- The same finite action, viewed on the underlying real spinor space. -/
noncomputable def realSpinorAction (A : DiracMatrix) : RealSpinorOperator :=
  LinearMap.restrictScalars ℝ (spinorAction A)

theorem realSpinorAction_mul (A B : DiracMatrix) :
    (realSpinorAction A).comp (realSpinorAction B) =
      realSpinorAction (A * B) := by
  have h := spinorAction_mul A B
  apply LinearMap.ext
  intro ψ
  have hψ := congrArg
    (fun T : SpinorCarrier →ₗ[ℂ] SpinorCarrier => T ψ) h
  simpa [realSpinorAction, LinearMap.comp_apply] using hψ

theorem realSpinorAction_sq_of (A : DiracMatrix)
    (hA : A * A = -(1 : DiracMatrix)) :
    (realSpinorAction A).comp (realSpinorAction A) =
      -(LinearMap.id : RealSpinorOperator) := by
  have h := spinorAction_sq_of A hA
  apply LinearMap.ext
  intro ψ
  have hψ := congrArg
    (fun T : SpinorCarrier →ₗ[ℂ] SpinorCarrier => T ψ) h
  simpa [realSpinorAction, LinearMap.comp_apply] using hψ

/-- The three quaternion units as actual real-linear complex structures on the
Dirac spinor carrier. -/
noncomputable def diracComplexI : RealSpinorOperator :=
  realSpinorAction InfoGeometry.Canonical.QuaternionEmbedding.quat_i

noncomputable def diracComplexJ : RealSpinorOperator :=
  realSpinorAction InfoGeometry.Canonical.QuaternionEmbedding.quat_j

noncomputable def diracComplexK : RealSpinorOperator :=
  realSpinorAction InfoGeometry.Canonical.QuaternionEmbedding.quat_k

theorem diracComplexI_sq :
    diracComplexI.comp diracComplexI =
      -(LinearMap.id : RealSpinorOperator) := by
  simpa [diracComplexI] using
    (realSpinorAction_sq_of
      InfoGeometry.Canonical.QuaternionEmbedding.quat_i
      InfoGeometry.Canonical.QuaternionEmbedding.quat_i_sq)

theorem diracComplexJ_sq :
    diracComplexJ.comp diracComplexJ =
      -(LinearMap.id : RealSpinorOperator) := by
  simpa [diracComplexJ] using
    (realSpinorAction_sq_of
      InfoGeometry.Canonical.QuaternionEmbedding.quat_j
      InfoGeometry.Canonical.QuaternionEmbedding.quat_j_sq)

theorem diracComplexK_sq :
    diracComplexK.comp diracComplexK =
      -(LinearMap.id : RealSpinorOperator) := by
  simpa [diracComplexK] using
    (realSpinorAction_sq_of
      InfoGeometry.Canonical.QuaternionEmbedding.quat_k
      InfoGeometry.Canonical.QuaternionEmbedding.quat_k_sq)

theorem diracComplexI_isRealComplexStructure :
    InfoGeometry.Canonical.IsRealComplexStructure diracComplexI :=
  diracComplexI_sq

theorem diracComplexJ_isRealComplexStructure :
    InfoGeometry.Canonical.IsRealComplexStructure diracComplexJ :=
  diracComplexJ_sq

theorem diracComplexK_isRealComplexStructure :
    InfoGeometry.Canonical.IsRealComplexStructure diracComplexK :=
  diracComplexK_sq

theorem diracComplexI_comp_J :
    diracComplexI.comp diracComplexJ = diracComplexK := by
  calc
    diracComplexI.comp diracComplexJ =
        realSpinorAction
          (InfoGeometry.Canonical.QuaternionEmbedding.quat_i *
            InfoGeometry.Canonical.QuaternionEmbedding.quat_j) :=
      realSpinorAction_mul _ _
    _ = diracComplexK := by
      rw [InfoGeometry.Canonical.QuaternionEmbedding.quat_ij_eq_k]

theorem diracComplexJ_comp_K :
    diracComplexJ.comp diracComplexK = diracComplexI := by
  calc
    diracComplexJ.comp diracComplexK =
        realSpinorAction
          (InfoGeometry.Canonical.QuaternionEmbedding.quat_j *
            InfoGeometry.Canonical.QuaternionEmbedding.quat_k) :=
      realSpinorAction_mul _ _
    _ = diracComplexI := by
      rw [InfoGeometry.Canonical.QuaternionEmbedding.quat_jk_eq_i]

theorem diracComplexK_comp_I :
    diracComplexK.comp diracComplexI = diracComplexJ := by
  calc
    diracComplexK.comp diracComplexI =
        realSpinorAction
          (InfoGeometry.Canonical.QuaternionEmbedding.quat_k *
            InfoGeometry.Canonical.QuaternionEmbedding.quat_i) :=
      realSpinorAction_mul _ _
    _ = diracComplexJ := by
      rw [InfoGeometry.Canonical.QuaternionEmbedding.quat_ki_eq_j]

theorem diracComplexJ_comp_I :
    diracComplexJ.comp diracComplexI = -diracComplexK := by
  have h := QuaternionicOperatorFrame.j_mul_i diracQuaternionicOperatorFrame
  calc
    diracComplexJ.comp diracComplexI =
        realSpinorAction
          (InfoGeometry.Canonical.QuaternionEmbedding.quat_j *
            InfoGeometry.Canonical.QuaternionEmbedding.quat_i) :=
      realSpinorAction_mul _ _
    _ = realSpinorAction
        (-InfoGeometry.Canonical.QuaternionEmbedding.quat_k) := by
      rw [h]
    _ = -diracComplexK := by
      simp [diracComplexK, realSpinorAction]

/-! ## Finite Hermitian/skew-Hermitian operator decomposition -/

/-- Hermitian part of a finite complex matrix operator. -/
def operatorHermitianPart (A : DiracMatrix) : DiracMatrix :=
  (2 : ℂ)⁻¹ • (A + Matrix.conjTranspose A)

/-- Skew-Hermitian part of a finite complex matrix operator. -/
def operatorSkewHermitianPart (A : DiracMatrix) : DiracMatrix :=
  (2 : ℂ)⁻¹ • (A - Matrix.conjTranspose A)

theorem operatorHermitian_skewHermitian_decomposition (A : DiracMatrix) :
    operatorHermitianPart A + operatorSkewHermitianPart A = A := by
  unfold operatorHermitianPart operatorSkewHermitianPart
  module

theorem operatorHermitianPart_isHermitian (A : DiracMatrix) :
    (operatorHermitianPart A).IsHermitian := by
  unfold operatorHermitianPart
  rw [Matrix.IsHermitian, Matrix.conjTranspose_smul,
    Matrix.conjTranspose_add, Matrix.conjTranspose_conjTranspose]
  norm_num
  module

theorem operatorSkewHermitianPart_conjTranspose (A : DiracMatrix) :
    Matrix.conjTranspose (operatorSkewHermitianPart A) =
      -operatorSkewHermitianPart A := by
  unfold operatorSkewHermitianPart
  rw [Matrix.conjTranspose_smul, Matrix.conjTranspose_sub,
    Matrix.conjTranspose_conjTranspose]
  norm_num
  module

/-- Existing Pauli soldering is the Hermitian 2 by 2 representative of a
real four-vector. -/
theorem pauliSoldering_real_isHermitian (E px py pz : ℝ) :
    Matrix.conjTranspose
        (InfoGeometry.Quantum.PauliSoldering.solder
          ((E : ℂ), (px : ℂ), (py : ℂ), (pz : ℂ))) =
      InfoGeometry.Quantum.PauliSoldering.solder
        ((E : ℂ), (px : ℂ), (py : ℂ), (pz : ℂ)) :=
  InfoGeometry.Quantum.PauliSoldering.solder_hermitian E px py pz

/-! ## Circular and chiral projectors -/

/-- The circular basis is the exact normal form of the chiral cone matrix. -/
theorem causalMatrix_circular_normal_form
    (xPlus xMinus z zbar : ℂ) :
    InfoGeometry.Quantum.CircularPauliCausalCone.causalMatrix
        xPlus xMinus z zbar =
      xPlus • InfoGeometry.Quantum.CircularPauliCausalCone.uPlus +
        xMinus • InfoGeometry.Quantum.CircularPauliCausalCone.uMinus +
        zbar • InfoGeometry.Quantum.CircularPauliCausalCone.sigmaPlus +
        z • InfoGeometry.Quantum.CircularPauliCausalCone.sigmaMinus :=
  InfoGeometry.Quantum.CircularPauliCausalCone.causalMatrix_circular_expansion
    xPlus xMinus z zbar

theorem circular_chiral_projector_sum :
    InfoGeometry.Quantum.CircularPauliCausalCone.uPlus +
        InfoGeometry.Quantum.CircularPauliCausalCone.uMinus =
      (1 : InfoGeometry.Quantum.CircularPauliCausalCone.Mat2) := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [InfoGeometry.Quantum.CircularPauliCausalCone.uPlus,
      InfoGeometry.Quantum.CircularPauliCausalCone.uMinus]

theorem circular_chiral_projectors_orthogonal :
    InfoGeometry.Quantum.CircularPauliCausalCone.uPlus *
        InfoGeometry.Quantum.CircularPauliCausalCone.uMinus = 0 ∧
      InfoGeometry.Quantum.CircularPauliCausalCone.uMinus *
        InfoGeometry.Quantum.CircularPauliCausalCone.uPlus = 0 :=
  ⟨InfoGeometry.Quantum.CircularPauliCausalCone.uPlus_mul_uMinus,
    InfoGeometry.Quantum.CircularPauliCausalCone.uMinus_mul_uPlus⟩

/-- The 4 by 4 chiral projectors owned by HodgeStar4D form a complete
orthogonal decomposition. -/
theorem hodge_chiral_projector_sum :
    InfoGeometry.Canonical.HodgeStar4D.P_SD +
        InfoGeometry.Canonical.HodgeStar4D.P_ASD =
      (1 : DiracMatrix) := by
  unfold InfoGeometry.Canonical.HodgeStar4D.P_SD
    InfoGeometry.Canonical.HodgeStar4D.P_ASD
  module

theorem hodge_chiral_projector_packet :
    InfoGeometry.Canonical.HodgeStar4D.P_SD *
          InfoGeometry.Canonical.HodgeStar4D.P_SD =
        InfoGeometry.Canonical.HodgeStar4D.P_SD ∧
      InfoGeometry.Canonical.HodgeStar4D.P_ASD *
          InfoGeometry.Canonical.HodgeStar4D.P_ASD =
        InfoGeometry.Canonical.HodgeStar4D.P_ASD ∧
      InfoGeometry.Canonical.HodgeStar4D.P_SD *
          InfoGeometry.Canonical.HodgeStar4D.P_ASD = 0 ∧
      InfoGeometry.Canonical.HodgeStar4D.P_SD +
          InfoGeometry.Canonical.HodgeStar4D.P_ASD =
        (1 : DiracMatrix) :=
  ⟨InfoGeometry.Canonical.HodgeStar4D.P_SD_idempotent,
    InfoGeometry.Canonical.HodgeStar4D.P_ASD_idempotent,
    InfoGeometry.Canonical.HodgeStar4D.P_SD_mul_P_ASD_eq_zero,
    hodge_chiral_projector_sum⟩

/-- The Lorentzian Hodge star is itself a complex structure on the finite
bivector/operator carrier. -/
theorem hodgeStar_is_realized_complex_structure
    (F : DiracMatrix) :
    InfoGeometry.Canonical.HodgeStar4D.hodgeStar
        (InfoGeometry.Canonical.HodgeStar4D.hodgeStar F) = -F :=
  InfoGeometry.Canonical.HodgeStar4D.hodgeStar_squared_eq_neg F

/-! ## Determinant and finite square-root readouts -/

/-- Positive branch of the determinant square root on the nonnegative
Minkowski cone. -/
noncomputable def pauliDeterminantSqrt
    (P : PauliParavector) : ℝ :=
  Real.sqrt P.minkowskiNormSq

theorem pauliDeterminantSqrt_nonneg (P : PauliParavector) :
    0 ≤ pauliDeterminantSqrt P :=
  Real.sqrt_nonneg _

theorem pauliDeterminantSqrt_sq_of_nonneg
    (P : PauliParavector) (hP : 0 ≤ P.minkowskiNormSq) :
    pauliDeterminantSqrt P ^ 2 = P.minkowskiNormSq := by
  simpa [pauliDeterminantSqrt] using Real.sq_sqrt hP

theorem pauliDeterminantSqrt_sq_eq_real_determinant
    (P : PauliParavector) (hP : 0 ≤ P.minkowskiNormSq) :
    pauliDeterminantSqrt P ^ 2 =
      (Matrix.det P.pauliMatrix).re := by
  rw [pauliDeterminantSqrt_sq_of_nonneg P hP,
    PauliParavector.det_pauliMatrix_eq_minkowskiNormSq]
  rfl

theorem pauliDeterminantSqrt_eq_zero_of_null
    (P : PauliParavector) (hP : P.minkowskiNormSq = 0) :
    pauliDeterminantSqrt P = 0 := by
  simp [pauliDeterminantSqrt, hP]

/-- The positive square-root readout for the two-by-two quaternionic Pauli
normal form. -/
noncomputable def pauliQuaternionDeterminantSqrt
    (q : ℝ × ℝ × ℝ × ℝ) : ℝ :=
  Real.sqrt
    (q.1 ^ 2 + q.2.1 ^ 2 + q.2.2.1 ^ 2 + q.2.2.2 ^ 2)

theorem pauliQuaternionDeterminantSqrt_sq
    (q : ℝ × ℝ × ℝ × ℝ) :
    pauliQuaternionDeterminantSqrt q ^ 2 =
      q.1 ^ 2 + q.2.1 ^ 2 + q.2.2.1 ^ 2 + q.2.2.2 ^ 2 := by
  have hq :
      0 ≤ q.1 ^ 2 + q.2.1 ^ 2 + q.2.2.1 ^ 2 + q.2.2.2 ^ 2 := by
    positivity
  simpa [pauliQuaternionDeterminantSqrt] using Real.sq_sqrt hq

theorem pauliQuaternionDeterminantSqrt_sq_eq_real_determinant
    (q : ℝ × ℝ × ℝ × ℝ) :
    pauliQuaternionDeterminantSqrt q ^ 2 =
      (Matrix.det
        (InfoGeometry.Clifford.QuaternionPauliRealForm.quaternionPauli q)).re := by
  rw [pauliQuaternionDeterminantSqrt_sq q,
    InfoGeometry.Clifford.QuaternionPauliRealForm.quaternionPauli_det]
  norm_num

end InfoGeometry.Canonical.QuaternionicOperatorComplexStructure
