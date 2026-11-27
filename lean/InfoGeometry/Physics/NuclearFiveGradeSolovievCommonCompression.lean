/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import Mathlib
import InfoGeometry.Algebra.FiniteSpinAlgebra
import InfoGeometry.Physics.NuclearFiveGradeCommonCarrierRepresentation
import InfoGeometry.Physics.SolovievQuasiparticlePhononEigenproblem
import InfoGeometry.Canonical.ZornCore

/-!
# Soloviev compression on the grade-preserving common carrier

The common representation carrier

`ℕ → (Fin 4 → NativeZorn)`

already supports the complete concrete two-mode five-grading, exact fermionic
CAR, exact phonon CCR, and the coefficientwise Zorn derivation action. This
file selects one occupied quasiparticle basis vector at phonon levels zero and
one and proves that the compressed represented Hamiltonian is exactly the
finite Soloviev QPNM matrix.

Thus the five-grade representation and the Soloviev compression live on the
same operator carrier.
-/

noncomputable section

namespace InfoGeometry.Physics.NuclearFiveGradeSolovievCommonCompression

open Matrix
open InfoGeometry.Algebra
open InfoGeometry.Canonical.SplitCliffordTwoModeCAR
open InfoGeometry.Physics.NuclearTwoModeFiveGradeLieModel
open InfoGeometry.Physics.NuclearFiveGradeCommonCarrierRepresentation
open InfoGeometry.Physics.SolovievQPNMEigenproblem

-- Keep the finite CAR matrices distinct from the native Zorn matrix carrier.
local notation "M4R" => InfoGeometry.Physics.NuclearTwoModeFiveGradeLieModel.M4R

abbrev ModelVector := InfoGeometry.Algebra.FiniteSpin.Vec2R

/-- Scalar copy of the native Zorn unit. -/
def scalarCoefficient (c : ℝ) : Coefficient where
  a := c
  v := fun _ => 0
  w := fun _ => 0
  b := c

/-- The selected quasiparticle mode is the `|10⟩` Jordan--Wigner basis vector. -/
def quasiparticleKet (c : ℝ) : FermionVector :=
  ![0, 0, scalarCoefficient c, 0]

@[simp] theorem quasiparticleKet_selected_a (c : ℝ) :
    (quasiparticleKet c 2).a = c := rfl

/-- Embed the zero- and one-phonon quasiparticle channels. -/
def modelEmbed : ModelVector →ₗ[ℝ] Carrier where
  toFun v
    | 0 => quasiparticleKet (v 0)
    | Nat.succ 0 => quasiparticleKet (v 1)
    | Nat.succ (Nat.succ _) => 0
  map_add' v w := by
    funext n i
    cases n with
    | zero =>
        fin_cases i <;> simp [quasiparticleKet, scalarCoefficient,
          InfoGeometry.Algebra.ZornVectorMatrix.add,
          InfoGeometry.Algebra.ZornVectorMatrix.smul,
          InfoGeometry.Algebra.ZornVectorMatrix.zero]
    | succ n =>
        cases n with
        | zero =>
            fin_cases i <;> simp [quasiparticleKet, scalarCoefficient,
              InfoGeometry.Algebra.ZornVectorMatrix.add,
              InfoGeometry.Algebra.ZornVectorMatrix.smul,
              InfoGeometry.Algebra.ZornVectorMatrix.zero]
        | succ n => exact (InfoGeometry.Algebra.ZornVectorMatrix.add_zero _).symm
  map_smul' c v := by
    funext n i
    cases n with
    | zero =>
        fin_cases i <;> simp [quasiparticleKet, scalarCoefficient,
          InfoGeometry.Algebra.ZornVectorMatrix.add,
          InfoGeometry.Algebra.ZornVectorMatrix.smul,
          InfoGeometry.Algebra.ZornVectorMatrix.zero]
    | succ n =>
        cases n with
        | zero =>
            fin_cases i <;> simp [quasiparticleKet, scalarCoefficient,
              InfoGeometry.Algebra.ZornVectorMatrix.add,
              InfoGeometry.Algebra.ZornVectorMatrix.smul,
              InfoGeometry.Algebra.ZornVectorMatrix.zero]
        | succ n => exact (InfoGeometry.Algebra.ZornVectorMatrix.smul_zero _).symm

@[simp] theorem modelEmbed_zero_level (v : ModelVector) :
    modelEmbed v 0 = quasiparticleKet (v 0) := rfl

@[simp] theorem modelEmbed_one_level (v : ModelVector) :
    modelEmbed v 1 = quasiparticleKet (v 1) := rfl

@[simp] theorem modelEmbed_high_level (v : ModelVector) (n : ℕ) :
    modelEmbed v (n + 2) = 0 := by
  rfl

/-- Read the scalar coefficient of the selected quasiparticle basis vector. -/
def modelReadout : Carrier →ₗ[ℝ] ModelVector where
  toFun ψ := ![(ψ 0 2).a, (ψ 1 2).a]
  map_add' ψ φ := by
    ext i
    fin_cases i <;>
      simp [InfoGeometry.Algebra.ZornVectorMatrix.add]
  map_smul' c ψ := by
    ext i
    fin_cases i <;>
      simp [InfoGeometry.Algebra.ZornVectorMatrix.smul]

@[simp] theorem modelReadout_modelEmbed (v : ModelVector) :
    modelReadout (modelEmbed v) = v := by
  ext i
  fin_cases i <;> rfl

/-- Model-space projection on the common carrier. -/
def modelProjection : Operator :=
  modelEmbed.comp modelReadout

@[simp] theorem modelProjection_modelEmbed (v : ModelVector) :
    modelProjection (modelEmbed v) = modelEmbed v := by
  change modelEmbed (modelReadout (modelEmbed v)) = modelEmbed v
  rw [modelReadout_modelEmbed]

/-- The common model projection is idempotent. -/
theorem modelProjection_idempotent :
    modelProjection * modelProjection = modelProjection := by
  apply LinearMap.ext
  intro ψ
  change modelEmbed
      (modelReadout (modelEmbed (modelReadout ψ))) =
    modelEmbed (modelReadout ψ)
  rw [modelReadout_modelEmbed]

/-- Explicit first-mode occupation matrix. -/
theorem number1_eq_diagonal :
    number1 =
      !![0, 0, 0, 0;
          0, 0, 0, 0;
          0, 0, 1, 0;
          0, 0, 0, 1] := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [number1, a1, a1Dag, Matrix.mul_apply,
      Fin.sum_univ_four, Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.cons_val_two, Matrix.cons_val_three, Fin.cons]

/-- The selected quasiparticle ket has first-mode occupation one. -/
theorem fermionAction_number1_quasiparticleKet (c : ℝ) :
    fermionAction number1 (quasiparticleKet c) = quasiparticleKet c := by
  rw [number1_eq_diagonal]
  funext i
  fin_cases i <;>
    simp [fermionAction, quasiparticleKet, scalarCoefficient,
      Fin.sum_univ_four, InfoGeometry.Algebra.ZornVectorMatrix.smul,
      InfoGeometry.Algebra.ZornVectorMatrix.zero,
      InfoGeometry.Algebra.ZornVectorMatrix.add,
      fermionAction_apply]

/-- Represented quasiparticle number. -/
def quasiparticleNumber : Operator :=
  representation number1

/-- The embedded model sector has exactly one quasiparticle. -/
@[simp] theorem quasiparticleNumber_modelEmbed (v : ModelVector) :
    quasiparticleNumber (modelEmbed v) = modelEmbed v := by
  funext n
  cases n with
  | zero =>
      simpa [quasiparticleNumber, representation, occupationLift] using
        fermionAction_number1_quasiparticleKet (v 0)
  | succ n =>
      cases n with
      | zero =>
          simpa [quasiparticleNumber, representation, occupationLift] using
            fermionAction_number1_quasiparticleKet (v 1)
      | succ n =>
          simp [quasiparticleNumber, representation, occupationLift]

/-- Phonon number. -/
def phononNumber : Operator :=
  phononCreation * phononAnnihilation

/-- Readout of the quasiparticle-number term. -/
@[simp] theorem readout_quasiparticleNumber_modelEmbed (v : ModelVector) :
    modelReadout (quasiparticleNumber (modelEmbed v)) = v := by
  rw [quasiparticleNumber_modelEmbed, modelReadout_modelEmbed]

/-- Readout of the phonon-number term. -/
@[simp] theorem readout_phononNumber_modelEmbed (C D : ℝ) :
    modelReadout (phononNumber (modelEmbed ![C, D])) = ![0, D] := by
  ext i
  fin_cases i <;>
    simp [phononNumber, modelReadout, modelEmbed, quasiparticleKet,
      scalarCoefficient, phononCreation, phononAnnihilation,
      InfoGeometry.Algebra.ZornVectorMatrix.zero,
      Module.End.mul_apply]

/-- Readout of one phonon creation. -/
@[simp] theorem readout_phononCreation_modelEmbed (C D : ℝ) :
    modelReadout (phononCreation (modelEmbed ![C, D])) = ![0, C] := by
  ext i
  fin_cases i <;>
    simp [modelReadout, modelEmbed, quasiparticleKet,
      scalarCoefficient, phononCreation,
      InfoGeometry.Algebra.ZornVectorMatrix.zero,
      InfoGeometry.Algebra.ZornVectorMatrix.smul,
      InfoGeometry.Algebra.ZornVectorMatrix.zero,
      InfoGeometry.Algebra.ZornVectorMatrix.add] <;> rfl

/-- Readout of one phonon annihilation. -/
@[simp] theorem readout_phononAnnihilation_modelEmbed (C D : ℝ) :
    modelReadout (phononAnnihilation (modelEmbed ![C, D])) = ![D, 0] := by
  ext i
  fin_cases i <;>
    simp [modelReadout, modelEmbed, quasiparticleKet,
      scalarCoefficient, phononAnnihilation,
      InfoGeometry.Algebra.ZornVectorMatrix.zero,
      InfoGeometry.Algebra.ZornVectorMatrix.smul]

/-- Full represented quasiparticle--phonon Hamiltonian. -/
def fullHamiltonian (Eqp omega V : ℝ) : Operator :=
  Eqp • quasiparticleNumber + omega • phononNumber +
    V • (phononCreation + phononAnnihilation)

/-- Compression of the represented Hamiltonian. -/
def compressedAction (Eqp omega V : ℝ) :
    ModelVector →ₗ[ℝ] ModelVector :=
  modelReadout.comp ((fullHamiltonian Eqp omega V).comp modelEmbed)

/-- Full compressed action as a vector identity. -/
theorem compressedAction_vector
    (Eqp omega V C D : ℝ) :
    compressedAction Eqp omega V ![C, D] =
      ![Eqp * C + V * D, V * C + (Eqp + omega) * D] := by
  change modelReadout
      (fullHamiltonian Eqp omega V (modelEmbed ![C, D])) = _
  simp [fullHamiltonian] <;> ring

/-- Zero-phonon readout. -/
theorem compressedAction_zero
    (Eqp omega V C D : ℝ) :
    compressedAction Eqp omega V ![C, D] 0 = Eqp * C + V * D := by
  rw [compressedAction_vector]
  rfl

/-- One-phonon readout. -/
theorem compressedAction_one
    (Eqp omega V C D : ℝ) :
    compressedAction Eqp omega V ![C, D] 1 =
      V * C + (Eqp + omega) * D := by
  rw [compressedAction_vector]
  rfl

/-- Main same-carrier compression theorem. -/
theorem compressedAction_eq_qpnm_mulVec
    (Eqp omega V C D : ℝ) :
    compressedAction Eqp omega V ![C, D] =
      mulVec (qpnmMatrix Eqp omega V) ![C, D] := by
  rw [compressedAction_vector]
  ext i
  fin_cases i <;>
    simp [qpnmMatrix, mulVec, dotProduct, Fin.sum_univ_two] <;>
    ring

/-- Exact projected-Hamiltonian theorem on the represented common carrier. -/
theorem projected_fullHamiltonian_on_model
    (Eqp omega V C D : ℝ) :
    modelProjection
        (fullHamiltonian Eqp omega V
          (modelProjection (modelEmbed ![C, D]))) =
      modelEmbed (mulVec (qpnmMatrix Eqp omega V) ![C, D]) := by
  rw [modelProjection_modelEmbed]
  change modelEmbed (compressedAction Eqp omega V ![C, D]) = _
  rw [compressedAction_eq_qpnm_mulVec]

/-- Complete same-carrier closure packet. -/
theorem five_grade_soloviev_same_carrier_packet
    (Eqp omega V C D : ℝ) :
    modelProjection * modelProjection = modelProjection ∧
      RepresentedHasGrade 2 (representation pairCreation) ∧
      RepresentedHasGrade (-2) (representation pairAnnihilation) ∧
      modelProjection
          (fullHamiltonian Eqp omega V
            (modelProjection (modelEmbed ![C, D]))) =
        modelEmbed (mulVec (qpnmMatrix Eqp omega V) ![C, D]) := by
  exact ⟨modelProjection_idempotent,
    representation_preserves_grade pairCreation_grade,
    representation_preserves_grade pairAnnihilation_grade,
    projected_fullHamiltonian_on_model Eqp omega V C D⟩

/-! ## Explicit SO(2) Unitary/Schur Decoupling Flow & Wegner Flow on `M2R` and `Carrier` -/

/-- `2 × 2` matrix commutator on `M2R`. -/
def comm (A B : M2R) : M2R := A * B - B * A

/-- Algebraic `SO(2)` rotation matrix parameterized by `(c, s)`. -/
def rotUAlg (c s : ℝ) : M2R :=
  !![c, -s; s, c]

/-- Trigonometric `SO(2)` rotation matrix `rotU θ`. -/
def rotU (θ : ℝ) : M2R :=
  !![Real.cos θ, -Real.sin θ; Real.sin θ, Real.cos θ]

theorem rotU_eq_rotUAlg (θ : ℝ) :
    rotU θ = rotUAlg (Real.cos θ) (Real.sin θ) := rfl

theorem rotUAlg_transpose (c s : ℝ) :
    (rotUAlg c s)ᵀ = rotUAlg c (-s) := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [rotUAlg]

theorem rotUAlg_mul (c₁ s₁ c₂ s₂ : ℝ) :
    rotUAlg c₁ s₁ * rotUAlg c₂ s₂ =
      rotUAlg (c₁ * c₂ - s₁ * s₂) (s₁ * c₂ + c₁ * s₂) := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [rotUAlg, Matrix.mul_apply, Fin.sum_univ_two] <;> ring

theorem rotUAlg_mul_transpose (c s : ℝ) (h : c ^ 2 + s ^ 2 = 1) :
    rotUAlg c s * (rotUAlg c s)ᵀ = 1 := by
  rw [rotUAlg_transpose, rotUAlg_mul]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [rotUAlg] <;> nlinarith

theorem rotUAlg_transpose_mul (c s : ℝ) (h : c ^ 2 + s ^ 2 = 1) :
    (rotUAlg c s)ᵀ * rotUAlg c s = 1 := by
  rw [rotUAlg_transpose, rotUAlg_mul]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [rotUAlg] <;> nlinarith

theorem rotU_mul_transpose (θ : ℝ) :
    rotU θ * (rotU θ)ᵀ = 1 :=
  rotUAlg_mul_transpose (Real.cos θ) (Real.sin θ) (Real.cos_sq_add_sin_sq θ)

theorem rotU_transpose_mul (θ : ℝ) :
    (rotU θ)ᵀ * rotU θ = 1 :=
  rotUAlg_transpose_mul (Real.cos θ) (Real.sin θ) (Real.cos_sq_add_sin_sq θ)

theorem rotU_zero : rotU 0 = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [rotU]

theorem rotU_neg (θ : ℝ) : rotU (-θ) = (rotU θ)ᵀ := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [rotU]

theorem rotU_group_law (θ₁ θ₂ : ℝ) :
    rotU (θ₁ + θ₂) = rotU θ₁ * rotU θ₂ := by
  rw [rotU_eq_rotUAlg, rotU_eq_rotUAlg, rotU_eq_rotUAlg, rotUAlg_mul]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [rotUAlg, Real.cos_add, Real.sin_add]

theorem rotU_mul_neg (θ : ℝ) :
    rotU θ * rotU (-θ) = 1 := by
  rw [rotU_neg, rotU_mul_transpose]

theorem rotU_neg_mul (θ : ℝ) :
    rotU (-θ) * rotU θ = 1 := by
  rw [rotU_neg, rotU_transpose_mul]

/-- Dressed Soloviev Hamiltonian under `SO(2)` rotation `rotU θ`. -/
def dressedQPNM (Eqp omega V θ : ℝ) : M2R :=
  rotU θ * qpnmMatrix Eqp omega V * (rotU θ)ᵀ

/-- Dressed traceless BdG longitudinal coordinate `ξ(θ)`. -/
def dressedBdGXi (omega V θ : ℝ) : ℝ :=
  (-omega / 2) * Real.cos (2 * θ) - V * Real.sin (2 * θ)

/-- Dressed off-diagonal quasiparticle-phonon coupling `V_eff(θ)`. -/
def dressedV (omega V θ : ℝ) : ℝ :=
  (-omega / 2) * Real.sin (2 * θ) + V * Real.cos (2 * θ)

/-- Dressed quasiparticle weight `E₁(θ)`. -/
def dressedE1 (Eqp omega V θ : ℝ) : ℝ :=
  (Eqp + omega / 2) + dressedBdGXi omega V θ

/-- Dressed phonon-dressed weight `E₂(θ)`. -/
def dressedE2 (Eqp omega V θ : ℝ) : ℝ :=
  (Eqp + omega / 2) - dressedBdGXi omega V θ

/-- Explicit entrywise form of `dressedQPNM`. -/
theorem dressedQPNM_eq (Eqp omega V θ : ℝ) :
    dressedQPNM Eqp omega V θ =
      !![dressedE1 Eqp omega V θ, dressedV omega V θ;
         dressedV omega V θ, dressedE2 Eqp omega V θ] := by
  have hcos2 : Real.cos (2 * θ) = (Real.cos θ) ^ 2 - (Real.sin θ) ^ 2 := by
    rw [two_mul, Real.cos_add]; ring
  have hsin2 : Real.sin (2 * θ) = 2 * Real.sin θ * Real.cos θ := by
    rw [two_mul, Real.sin_add]; ring
  have hpyth : (Real.cos θ) ^ 2 + (Real.sin θ) ^ 2 = 1 := Real.cos_sq_add_sin_sq θ
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [dressedQPNM, rotU, qpnmMatrix, dressedE1, dressedE2,
      dressedBdGXi, dressedV, hcos2, hsin2, Matrix.mul_apply, Fin.sum_univ_two]
  · linear_combination (Eqp + omega / 2) * hpyth
  · ring
  · ring
  · linear_combination (Eqp + omega / 2) * hpyth

theorem dressedQPNM_zero (Eqp omega V : ℝ) :
    dressedQPNM Eqp omega V 0 = qpnmMatrix Eqp omega V := by
  simp [dressedQPNM, rotU_zero]

theorem dressedQPNM_transpose (Eqp omega V θ : ℝ) :
    (dressedQPNM Eqp omega V θ)ᵀ = dressedQPNM Eqp omega V θ := by
  rw [dressedQPNM_eq]
  ext i j
  fin_cases i <;> fin_cases j <;> simp

/-- Exact trace invariance along the `SO(2)` flow. -/
theorem dressedQPNM_trace (Eqp omega V θ : ℝ) :
    (dressedQPNM Eqp omega V θ).trace = 2 * Eqp + omega := by
  rw [dressedQPNM_eq]
  simp [Matrix.trace, dressedE1, dressedE2]
  ring

theorem dressedQPNM_trace_eq (Eqp omega V θ : ℝ) :
    (dressedQPNM Eqp omega V θ).trace = (qpnmMatrix Eqp omega V).trace := by
  rw [dressedQPNM_trace]
  simp [qpnmMatrix, Matrix.trace]
  ring

/-- Exact BdG-radius invariance: `ξ(θ)^2 + V_eff(θ)^2 = (-ω/2)^2 + V^2`. -/
theorem dressed_bdg_radius_invariant (omega V θ : ℝ) :
    (dressedBdGXi omega V θ) ^ 2 + (dressedV omega V θ) ^ 2 =
      (-omega / 2) ^ 2 + V ^ 2 := by
  have hpyth : Real.cos (2 * θ) ^ 2 + Real.sin (2 * θ) ^ 2 = 1 :=
    Real.cos_sq_add_sin_sq (2 * θ)
  dsimp [dressedBdGXi, dressedV]
  nlinarith [hpyth]

/-- Exact determinant invariance along the `SO(2)` flow. -/
theorem dressedQPNM_det (Eqp omega V θ : ℝ) :
    (dressedQPNM Eqp omega V θ).det = Eqp * (Eqp + omega) - V ^ 2 := by
  have hrad := dressed_bdg_radius_invariant omega V θ
  rw [dressedQPNM_eq]
  simp [Matrix.det_fin_two, dressedE1, dressedE2]
  calc
    (Eqp + omega / 2 + dressedBdGXi omega V θ) *
          (Eqp + omega / 2 - dressedBdGXi omega V θ) -
        dressedV omega V θ * dressedV omega V θ
      = (Eqp + omega / 2) ^ 2 -
          ((dressedBdGXi omega V θ) ^ 2 + (dressedV omega V θ) ^ 2) := by ring
    _ = (Eqp + omega / 2) ^ 2 - ((-omega / 2) ^ 2 + V ^ 2) := by rw [hrad]
    _ = Eqp * (Eqp + omega) - V ^ 2 := by ring

theorem dressedQPNM_det_eq (Eqp omega V θ : ℝ) :
    (dressedQPNM Eqp omega V θ).det = (qpnmMatrix Eqp omega V).det := by
  rw [dressedQPNM_det]
  simp [qpnmMatrix, Matrix.det_fin_two]
  ring

/-- Exact Schur/Bogoliubov decoupling condition: `V_eff(θ) = 0 ↔ V cos(2θ) = (ω/2) sin(2θ)`. -/
theorem dressedV_eq_zero_iff (omega V θ : ℝ) :
    dressedV omega V θ = 0 ↔ V * Real.cos (2 * θ) = (omega / 2) * Real.sin (2 * θ) := by
  dsimp [dressedV]
  constructor <;> intro h <;> linarith

/-- When the Schur decoupling angle holds, `dressedQPNM` is strictly diagonal. -/
theorem dressedQPNM_diagonal_of_decoupled (Eqp omega V θ : ℝ)
    (hdec : V * Real.cos (2 * θ) = (omega / 2) * Real.sin (2 * θ)) :
    dressedQPNM Eqp omega V θ =
      !![dressedE1 Eqp omega V θ, 0; 0, dressedE2 Eqp omega V θ] := by
  rw [dressedQPNM_eq, (dressedV_eq_zero_iff omega V θ).mpr hdec]

/-- Continuous **Wegner differential flow**:
`d/dθ (dressedQPNM Eqp omega V θ) = [!![0, -1; 1, 0], dressedQPNM Eqp omega V θ]`. -/
theorem hasDerivAt_dressedQPNM (Eqp omega V θ : ℝ) :
    HasDerivAt (fun t => dressedQPNM Eqp omega V t)
      (comm !![0, -1; 1, 0] (dressedQPNM Eqp omega V θ)) θ := by
  have h_two : HasDerivAt (fun s : ℝ => 2 * s) 2 θ := by
    simpa using (hasDerivAt_id θ).const_mul 2
  have hcos2 : HasDerivAt (fun t => Real.cos (2 * t)) (-Real.sin (2 * θ) * 2) θ :=
    (Real.hasDerivAt_cos (2 * θ)).comp θ h_two
  have hsin2 : HasDerivAt (fun t => Real.sin (2 * t)) (Real.cos (2 * θ) * 2) θ :=
    (Real.hasDerivAt_sin (2 * θ)).comp θ h_two
  have h_xi : HasDerivAt (fun t => dressedBdGXi omega V t)
      (-2 * dressedV omega V θ) θ := by
    have h := (hcos2.const_mul (-omega / 2)).sub (hsin2.const_mul V)
    rw [show (-omega / 2) * (-Real.sin (2 * θ) * 2) - V * (Real.cos (2 * θ) * 2) =
        -2 * dressedV omega V θ by dsimp [dressedV]; ring] at h
    exact h
  have h_v : HasDerivAt (fun t => dressedV omega V t)
      (2 * dressedBdGXi omega V θ) θ := by
    have h := (hsin2.const_mul (-omega / 2)).add (hcos2.const_mul V)
    rw [show (-omega / 2) * (Real.cos (2 * θ) * 2) + V * (-Real.sin (2 * θ) * 2) =
        2 * dressedBdGXi omega V θ by dsimp [dressedBdGXi]; ring] at h
    exact h
  have h_e1 : HasDerivAt (fun t => dressedE1 Eqp omega V t)
      (-2 * dressedV omega V θ) θ := by
    have h := (hasDerivAt_const θ (Eqp + omega / 2)).add h_xi
    rw [zero_add] at h
    exact h
  have h_e2 : HasDerivAt (fun t => dressedE2 Eqp omega V t)
      (2 * dressedV omega V θ) θ := by
    have h := (hasDerivAt_const θ (Eqp + omega / 2)).sub h_xi
    rw [zero_sub, neg_mul_eq_neg_mul, neg_neg] at h
    exact h
  have h_comm_eq :
      comm !![0, -1; 1, 0] (dressedQPNM Eqp omega V θ) =
        !![-2 * dressedV omega V θ, 2 * dressedBdGXi omega V θ;
           2 * dressedBdGXi omega V θ, 2 * dressedV omega V θ] := by
    rw [dressedQPNM_eq]
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [comm, dressedE1, dressedE2] <;>
      ring
  rw [h_comm_eq]
  simp_rw [dressedQPNM_eq]
  change HasDerivAt
      (fun t => !![dressedE1 Eqp omega V t, dressedV omega V t;
                   dressedV omega V t, dressedE2 Eqp omega V t])
      (!![-2 * dressedV omega V θ, 2 * dressedBdGXi omega V θ;
          2 * dressedBdGXi omega V θ, 2 * dressedV omega V θ]) θ
  refine hasDerivAt_pi.2 fun i => hasDerivAt_pi.2 fun j => ?_
  fin_cases i <;> fin_cases j
  · simpa using h_e1
  · simpa using h_v
  · simpa using h_v
  · simpa using h_e2

/-- Lift of the `SO(2)` rotation `rotU θ` to the common operator `Carrier`. -/
def U_op (θ : ℝ) : Operator :=
  (1 - modelProjection) + modelEmbed.comp ((Matrix.toLin' (rotU θ)).comp modelReadout)

theorem U_op_apply (θ : ℝ) (ψ : Carrier) :
    U_op θ ψ = ψ - modelProjection ψ + modelEmbed (Matrix.toLin' (rotU θ) (modelReadout ψ)) := rfl

theorem U_op_modelEmbed (θ : ℝ) (v : ModelVector) :
    U_op θ (modelEmbed v) = modelEmbed (Matrix.toLin' (rotU θ) v) := by
  rw [U_op_apply, modelProjection_modelEmbed, sub_self, zero_add, modelReadout_modelEmbed]

theorem U_op_modelProjection (θ : ℝ) (ψ : Carrier) :
    U_op θ (modelProjection ψ) = modelEmbed (Matrix.toLin' (rotU θ) (modelReadout ψ)) := by
  change U_op θ (modelEmbed (modelReadout ψ)) = _
  exact U_op_modelEmbed θ (modelReadout ψ)

theorem modelProjection_U_op (θ : ℝ) (ψ : Carrier) :
    modelProjection (U_op θ ψ) = modelEmbed (Matrix.toLin' (rotU θ) (modelReadout ψ)) := by
  rw [U_op_apply, map_add, map_sub]
  have hpp : modelProjection (modelProjection ψ) = modelProjection ψ :=
    LinearMap.congr_fun modelProjection_idempotent ψ
  rw [hpp, sub_self, zero_add, modelProjection_modelEmbed]

theorem modelReadout_U_op (θ : ℝ) (ψ : Carrier) :
    modelReadout (U_op θ ψ) = Matrix.toLin' (rotU θ) (modelReadout ψ) := by
  rw [U_op_apply, map_add, map_sub]
  have hrmp : modelReadout (modelProjection ψ) = modelReadout ψ := by
    change modelReadout (modelEmbed (modelReadout ψ)) = modelReadout ψ
    exact modelReadout_modelEmbed _
  rw [hrmp, sub_self, zero_add, modelReadout_modelEmbed]

theorem U_op_group_law (θ₁ θ₂ : ℝ) :
    U_op θ₁ * U_op θ₂ = U_op (θ₁ + θ₂) := by
  apply LinearMap.ext
  intro ψ
  change U_op θ₁ (U_op θ₂ ψ) = U_op (θ₁ + θ₂) ψ
  rw [U_op_apply θ₁ (U_op θ₂ ψ), modelProjection_U_op, modelReadout_U_op]
  rw [U_op_apply θ₂ ψ]
  have hrot : Matrix.toLin' (rotU θ₁) (Matrix.toLin' (rotU θ₂) (modelReadout ψ)) =
      Matrix.toLin' (rotU (θ₁ + θ₂)) (modelReadout ψ) := by
    rw [rotU_group_law, Matrix.toLin'_mul]
    rfl
  rw [hrot, U_op_apply]
  abel

theorem U_op_zero : U_op 0 = 1 := by
  apply LinearMap.ext
  intro ψ
  rw [U_op_apply, rotU_zero, Matrix.toLin'_one, LinearMap.id_apply]
  change (ψ - modelProjection ψ) + modelProjection ψ = ψ
  abel

theorem U_op_mul_neg (θ : ℝ) : U_op θ * U_op (-θ) = 1 := by
  rw [U_op_group_law, add_neg_cancel, U_op_zero]

theorem U_op_neg_mul (θ : ℝ) : U_op (-θ) * U_op θ = 1 := by
  rw [U_op_group_law, neg_add_cancel, U_op_zero]

theorem compressedAction_eq_toLin' (Eqp omega V : ℝ) :
    compressedAction Eqp omega V = Matrix.toLin' (qpnmMatrix Eqp omega V) := by
  apply LinearMap.ext
  intro v
  have hv : v = ![v 0, v 1] := by
    ext i
    fin_cases i <;> rfl
  rw [hv, compressedAction_eq_qpnm_mulVec, Matrix.toLin'_apply]

/-- Exact lifted unitary flow intertwining on the common operator `Carrier`:
`P (U(θ) H U(-θ)) P = modelEmbed ∘ dressedQPNM(θ) ∘ modelReadout`. -/
theorem flow_intertwining_on_modelProjection (Eqp omega V θ : ℝ) :
    modelProjection * (U_op θ * fullHamiltonian Eqp omega V * U_op (-θ)) * modelProjection =
      modelEmbed.comp ((Matrix.toLin' (dressedQPNM Eqp omega V θ)).comp modelReadout) := by
  apply LinearMap.ext
  intro ψ
  change modelProjection (U_op θ (fullHamiltonian Eqp omega V (U_op (-θ) (modelProjection ψ)))) =
    modelEmbed (Matrix.toLin' (dressedQPNM Eqp omega V θ) (modelReadout ψ))
  rw [U_op_modelProjection, modelProjection_U_op]
  have h_comp : modelReadout (fullHamiltonian Eqp omega V
      (modelEmbed (Matrix.toLin' (rotU (-θ)) (modelReadout ψ)))) =
      compressedAction Eqp omega V (Matrix.toLin' (rotU (-θ)) (modelReadout ψ)) := rfl
  rw [h_comp, compressedAction_eq_toLin']
  congr 1
  have h_dressed : dressedQPNM Eqp omega V θ = rotU θ * qpnmMatrix Eqp omega V * rotU (-θ) := by
    rw [rotU_neg]
    rfl
  rw [h_dressed, Matrix.toLin'_mul, Matrix.toLin'_mul]
  rfl

end InfoGeometry.Physics.NuclearFiveGradeSolovievCommonCompression
