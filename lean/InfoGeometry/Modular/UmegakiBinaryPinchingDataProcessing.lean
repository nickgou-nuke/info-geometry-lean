/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.Canonical.MatrixEntropyUnitaryOrbit
import InfoGeometry.Core.PeirceGrading
import InfoGeometry.OperatorAlgebra.PeirceSpine.Basic

/-! # Umegaki data processing for a noncommutative binary pinching

For a self-adjoint projection, Peirce pinching is the average of the identity
and conjugation by its unitary reflection. Convexity in the second argument
and unitary invariance of the full matrix Umegaki entropy therefore give the
binary pinching data-processing inequality when the first argument is fixed
by the projection. No diagonalization or commutativity of the density matrices
is assumed.
-/

noncomputable section

namespace InfoGeometry.Modular.UmegakiBinaryPinchingDataProcessing

open Matrix
open InfoGeometry.OperatorAlgebra.PeirceSpine
open InfoGeometry.Canonical.MatrixEntropyUnitaryOrbit
open InfoGeometry.OperatorAlgebra.NoncommutativeRenyi
open InfoGeometry.Core.PeirceGrading
open scoped Matrix MatrixOrder Matrix.Norms.L2Operator ComplexOrder

variable {n : Type*} [Fintype n] [DecidableEq n]
local notation "Mat" => Matrix n n ℂ

/-- The binary Peirce pinching associated with a projection. -/
def binaryPinching (P X : Mat) : Mat := evenGrade P X

/-- Peirce pinching is the average of identity and reflection conjugation. -/
theorem binaryPinching_eq_reflection_average (P X : Mat)
    (hP : P * P = P) (hPs : star P = P) :
    binaryPinching P X = (1 / 2 : ℝ) •
      (X + reflection P * X * star (reflection P)) := by
  have hp : IsIdempotentElem P := hP
  have hscaled := (InfoGeometry.Core.PeirceGrading.scaled_parts P X).1
  change X + reflection P * X * reflection P = 2 • evenGrade P X at hscaled
  have hstar : star (reflection P) = reflection P :=
    (InfoGeometry.Core.PeirceGrading.reflection_star (p := P)
      (isSelfAdjoint_iff.2 hPs)).star_eq
  unfold binaryPinching
  rw [hstar]
  have htwice : (2 : ℝ) • evenGrade P X = evenGrade P X + evenGrade P X :=
    two_smul ℝ (evenGrade P X)
  have hscaledAdd : X + reflection P * X * reflection P =
      evenGrade P X + evenGrade P X := by
    simpa only [two_smul] using hscaled
  have hscaledR : X + reflection P * X * reflection P =
      (2 : ℝ) • evenGrade P X := hscaledAdd.trans htwice.symm
  calc
    evenGrade P X = (1 / 2 : ℝ) • (evenGrade P X + evenGrade P X) := by
      rw [htwice.symm]
      rw [smul_smul]
      norm_num
    _ = (1 / 2 : ℝ) • (X + reflection P * X * reflection P) := by
      rw [hscaledR]
      rw [← htwice]

/-- An operator in the commutant of a self-adjoint projection is fixed by
conjugation with its Peirce reflection. This turns conserved commutant
observables in a projection-jump GKSL model into fixed observables for the
trace-orthogonality theorem below. -/
theorem reflection_conjugate_eq_self_of_commutes
    (P Y : Mat) (hP : P * P = P) (hPs : star P = P)
    (hYP : P * Y = Y * P) :
    reflection P * Y * star (reflection P) = Y := by
  have hp : IsStarProjection P := isStarProjection_iff'.2 ⟨hP, hPs⟩
  have hRstar : star (reflection P) = reflection P :=
    (reflection_star (p := P) hp.isSelfAdjoint).star_eq
  have hR2 : reflection P * reflection P = 1 :=
    reflection_sq hp.isIdempotentElem
  have hRY : reflection P * Y = Y * reflection P := by
    dsimp [reflection]
    noncomm_ring [hYP]
  rw [hRstar]
  calc
    reflection P * Y * reflection P =
        (reflection P * Y) * reflection P := rfl
    _ = (Y * reflection P) * reflection P := by rw [hRY]
    _ = Y := by rw [show (Y * reflection P) * reflection P =
        Y * (reflection P * reflection P) by noncomm_ring, hR2, mul_one]

/-- The residual of binary Peirce pinching is trace-orthogonal to every
operator fixed by the reflection. This is the finite-matrix conditional
expectation identity underlying both the Pythagorean law and conserved
commutant readouts. No commutativity between `X` and `Y` is assumed. -/
theorem trace_sub_binaryPinching_mul_of_reflection_fixed
    (P X Y : Mat) (hP : P * P = P) (hPs : star P = P)
    (hY : reflection P * Y * star (reflection P) = Y) :
    Matrix.trace ((X - binaryPinching P X) * Y) = 0 := by
  let R : Mat := reflection P
  have hRstar : star R = R := by
    exact (reflection_star (p := P)
      (isStarProjection_iff'.2 ⟨hP, hPs⟩).isSelfAdjoint).star_eq
  have hR2 : R * R = 1 :=
    reflection_sq (isStarProjection_iff'.2 ⟨hP, hPs⟩).isIdempotentElem
  have hY' : star R * Y * R = Y := by
    simpa [R, hRstar] using hY
  have hYcomm : R * Y = Y * R := by
    calc
      R * Y = R * Y * (R * R) := by rw [hR2, mul_one]
      _ = (R * Y * R) * R := by simp [mul_assoc]
      _ = (star R * Y * R) * R := by rw [hRstar]
      _ = Y * R := by rw [hY']
  have hRunit : R ∈ unitary Mat :=
    reflection_mem_unitary (isStarProjection_iff'.2 ⟨hP, hPs⟩)
  have hconj : Matrix.trace ((R * X * star R) * Y) = Matrix.trace (X * Y) := by
    have hprod : (R * X * star R) * Y = R * (X * Y) * star R := by
      rw [hRstar]
      calc
        (R * X * R) * Y = R * X * (R * Y) := by noncomm_ring
        _ = R * X * (Y * R) := by rw [hYcomm]
        _ = R * (X * Y) * R := by noncomm_ring
    rw [hprod]
    exact trace_unitary_conjugate ⟨R, hRunit⟩ (X * Y)
  have hconj' : Matrix.trace ((reflection P * X * star (reflection P)) * Y) =
      Matrix.trace (X * Y) := by simpa [R] using hconj
  rw [binaryPinching_eq_reflection_average P X hP hPs]
  simp only [Matrix.sub_mul, Matrix.add_mul, Matrix.smul_mul,
    Matrix.trace_sub, Matrix.trace_add, Matrix.trace_smul]
  rw [hconj']
  rw [smul_add, ← add_smul]
  norm_num

/-- A unitary conjugate of a strictly positive matrix is strictly positive. -/
private theorem unitary_conjugate_strictlyPositive (U : unitary Mat) (X : Mat)
    (hX : IsStrictlyPositive X) :
    IsStrictlyPositive ((U : Mat) * X * star (U : Mat)) := by
  exact (Unitary.isUnit_coe (U := U)).isStrictlyPositive_star_right_conjugate_iff.mpr hX

/-- Umegaki relative entropy decreases under binary Peirce pinching, provided
the reference state is fixed by that pinching. The matrices may be fully
noncommuting; the proof uses full matrix CFC logarithms through the existing
convexity and unitary-orbit theorems. -/
theorem umegaki_binary_pinching_data_processing
    (P ρ σ : Mat) (hP : P * P = P) (hPs : star P = P)
    (hρ : IsStrictlyPositive ρ) (hσ : IsStrictlyPositive σ)
    (hρP : ρ * P = P * ρ) :
    IsStrictlyPositive (binaryPinching P σ) ∧
      umegakiRelativeEntropy (Matrix.tracePositiveLinearMap n ℂ ℂ) ρ
          (binaryPinching P σ) ≤
        umegakiRelativeEntropy (Matrix.tracePositiveLinearMap n ℂ ℂ) ρ σ := by
  let R : Mat := reflection P
  have hp : IsStarProjection P := isStarProjection_iff'.2 ⟨hP, hPs⟩
  have hRstar : star R = R := by
    exact (reflection_star (p := P) hp.isSelfAdjoint).star_eq
  have hRunit : R ∈ unitary Mat := by
    exact reflection_mem_unitary hp
  let U : unitary Mat := ⟨R, hRunit⟩
  have hRsq : R * R = 1 := by
    dsimp [R]
    exact reflection_sq hp.isIdempotentElem
  have hRcomm : R * ρ = ρ * R := by
    apply sub_eq_zero.mp
    dsimp [R]
    rw [reflection_commutator, hρP]
    simp
  have hρfixed : (U : Mat) * ρ * star (U : Mat) = ρ := by
    change R * ρ * star R = ρ
    rw [hRstar]
    calc
      R * ρ * R = R * (ρ * R) := by rw [mul_assoc]
      _ = R * (R * ρ) := by rw [hRcomm]
      _ = (R * R) * ρ := by rw [← mul_assoc]
      _ = ρ := by rw [hRsq]; simp
  have hσconj : IsStrictlyPositive ((U : Mat) * σ * star (U : Mat)) :=
    unitary_conjugate_strictlyPositive U σ hσ
  have hpinch : binaryPinching P σ =
      (1 / 2 : ℝ) • σ + (1 / 2 : ℝ) • ((U : Mat) * σ * star (U : Mat)) := by
    rw [binaryPinching_eq_reflection_average P σ hP hPs]
    dsimp [U, R]
    simp only [smul_add]
  have hpinch_pos : IsStrictlyPositive (binaryPinching P σ) := by
    rw [hpinch]
    apply IsStrictlyPositive.add_nonneg
    · exact IsStrictlyPositive.smul (by norm_num) hσ
    · exact smul_nonneg (by norm_num) hσconj.nonneg
  have hconvex := umegakiRelativeEntropy_convex_second_argument
    ρ σ ((U : Mat) * σ * star (U : Mat)) (1 / 2 : ℝ)
    hρ hσ hσconj (by norm_num) (by norm_num)
  have horbit := umegakiRelativeEntropy_unitary_conjugate U ρ σ hρ hσ
  have hρorbit : (U : Mat) * ρ * star (U : Mat) = ρ := hρfixed
  have horbit' :
      umegakiRelativeEntropy (Matrix.tracePositiveLinearMap n ℂ ℂ) ρ σ =
      umegakiRelativeEntropy (Matrix.tracePositiveLinearMap n ℂ ℂ) ρ
        ((U : Mat) * σ * star (U : Mat)) := by
    simpa [hρorbit] using horbit
  have hconvex' :
      umegakiRelativeEntropy (Matrix.tracePositiveLinearMap n ℂ ℂ) ρ
          ((1 / 2 : ℝ) • σ + (1 / 2 : ℝ) • ((U : Mat) * σ * star (U : Mat))) ≤
        ((1 / 2 : ℝ) : ℂ) * umegakiRelativeEntropy
            (Matrix.tracePositiveLinearMap n ℂ ℂ) ρ σ +
          ((1 / 2 : ℝ) : ℂ) * umegakiRelativeEntropy
            (Matrix.tracePositiveLinearMap n ℂ ℂ) ρ ((U : Mat) * σ * star (U : Mat)) := by
    convert hconvex using 1 <;> norm_num
  refine ⟨hpinch_pos, ?_⟩
  rw [hpinch]
  calc
    umegakiRelativeEntropy (Matrix.tracePositiveLinearMap n ℂ ℂ) ρ
        ((1 / 2 : ℝ) • σ + (1 / 2 : ℝ) •
          ((U : Mat) * σ * star (U : Mat)))
      ≤ ((1 / 2 : ℝ) : ℂ) *
          umegakiRelativeEntropy (Matrix.tracePositiveLinearMap n ℂ ℂ) ρ σ +
        ((1 / 2 : ℝ) : ℂ) *
          umegakiRelativeEntropy (Matrix.tracePositiveLinearMap n ℂ ℂ) ρ
            ((U : Mat) * σ * star (U : Mat)) := hconvex'
    _ = umegakiRelativeEntropy (Matrix.tracePositiveLinearMap n ℂ ℂ) ρ σ := by
      rw [← horbit']
      push_cast
      rw [← add_mul]
      norm_num

/-- Exact relative-entropy Pythagoras for a binary Peirce conditional
expectation.  This is the general finite-dimensional complex-matrix version:
the source and reference need not commute with one another, while the
reference is fixed by the pinching. -/
theorem umegaki_binary_pinching_pythagorean
    (P ρ σ : Mat) (hP : P * P = P) (hPs : star P = P)
    (hρ : IsStrictlyPositive ρ) (hσ : IsStrictlyPositive σ)
    (hσP : σ * P = P * σ) :
    umegakiRelativeEntropy (Matrix.tracePositiveLinearMap n ℂ ℂ) ρ σ =
      umegakiRelativeEntropy (Matrix.tracePositiveLinearMap n ℂ ℂ) ρ
        (binaryPinching P ρ) +
      umegakiRelativeEntropy (Matrix.tracePositiveLinearMap n ℂ ℂ)
        (binaryPinching P ρ) σ := by
  let R : Mat := reflection P
  have hp : IsStarProjection P := isStarProjection_iff'.2 ⟨hP, hPs⟩
  have hRstar : star R = R :=
    (reflection_star (p := P) hp.isSelfAdjoint).star_eq
  have hRunit : R ∈ unitary Mat := reflection_mem_unitary hp
  let U : unitary Mat := ⟨R, hRunit⟩
  have hRsq : R * R = 1 := reflection_sq hp.isIdempotentElem
  have hU1 : (U : Mat) * star (U : Mat) = 1 := by
    change R * star R = 1
    rw [hRstar]
    exact hRsq
  have hU2 : star (U : Mat) * (U : Mat) = 1 := by
    change star R * R = 1
    rw [hRstar]
    exact hRsq
  have hσcomm : R * σ = σ * R := by
    apply sub_eq_zero.mp
    dsimp [R]
    rw [reflection_commutator, hσP]
    simp
  have hσfixed : (U : Mat) * σ * star (U : Mat) = σ := by
    change R * σ * star R = σ
    rw [hRstar]
    calc
      R * σ * R = R * (σ * R) := by rw [mul_assoc]
      _ = R * (R * σ) := by rw [hσcomm]
      _ = (R * R) * σ := by rw [← mul_assoc]
      _ = σ := by rw [hRsq]; simp
  have hρconj_pos : IsStrictlyPositive ((U : Mat) * ρ * star (U : Mat)) :=
    unitary_conjugate_strictlyPositive U ρ hρ
  have hpinch_avg : binaryPinching P ρ =
      (1 / 2 : ℝ) • ρ + (1 / 2 : ℝ) • ((U : Mat) * ρ * star (U : Mat)) := by
    rw [binaryPinching_eq_reflection_average P ρ hP hPs]
    dsimp [U, R]
    simp only [smul_add]
  have hρpinch_pos : IsStrictlyPositive (binaryPinching P ρ) := by
    rw [hpinch_avg]
    apply IsStrictlyPositive.add_nonneg
    · exact IsStrictlyPositive.smul (by norm_num) hρ
    · exact smul_nonneg (by norm_num) hρconj_pos.nonneg
  let φ := Unitary.conjStarAlgAut ℝ Mat U
  have hUeq : (U : Mat) = R := rfl
  have hφ_apply (X : Mat) : φ X = (U : Mat) * X * star (U : Mat) := by
    simp [φ, Unitary.conjStarAlgAut_apply]
  have hφ_invol (X : Mat) : φ (φ X) = X := by
    calc
      φ (φ X) = R * (R * X * R) * R := by
        rw [hφ_apply, hφ_apply]
        simp only [hUeq, hRstar]
      _ = (R * R) * X * (R * R) := by noncomm_ring
      _ = X := by rw [hRsq]; simp
  have hρpinch_fixed : (U : Mat) * binaryPinching P ρ * star (U : Mat) =
      binaryPinching P ρ := by
    change φ (binaryPinching P ρ) = binaryPinching P ρ
    rw [hpinch_avg]
    simp only [map_add, map_smul]
    rw [← hφ_apply ρ, hφ_invol]
    abel
  have hlog_pinched :
      CFC.log (binaryPinching P ρ) =
        (U : Mat) * CFC.log (binaryPinching P ρ) * star (U : Mat) := by
    rw [← log_unitary_conjugate U (binaryPinching P ρ) hρpinch_pos,
      hρpinch_fixed]
  have hlog_σ : CFC.log σ = (U : Mat) * CFC.log σ * star (U : Mat) := by
    rw [← log_unitary_conjugate U σ hσ, hσfixed]
  have h_entropy_form (a b : Mat) :
      umegakiRelativeEntropy (Matrix.tracePositiveLinearMap n ℂ ℂ) a b =
        Matrix.trace (a * (CFC.log a - CFC.log b)) := by
    rfl
  rw [h_entropy_form, h_entropy_form, h_entropy_form]
  have horth1 := trace_sub_binaryPinching_mul_of_reflection_fixed
    P ρ (CFC.log (binaryPinching P ρ)) hP hPs hlog_pinched.symm
  have horth2 := trace_sub_binaryPinching_mul_of_reflection_fixed
    P ρ (CFC.log σ) hP hPs hlog_σ.symm
  have horth1' : Matrix.trace (ρ * CFC.log (binaryPinching P ρ)) =
      Matrix.trace (binaryPinching P ρ * CFC.log (binaryPinching P ρ)) := by
    have h' : Matrix.trace (ρ * CFC.log (binaryPinching P ρ)) -
        Matrix.trace (binaryPinching P ρ * CFC.log (binaryPinching P ρ)) = 0 := by
      simpa [Matrix.sub_mul, Matrix.trace_sub] using horth1
    exact sub_eq_zero.mp h'
  have horth2' : Matrix.trace (ρ * CFC.log σ) =
      Matrix.trace (binaryPinching P ρ * CFC.log σ) := by
    have h' : Matrix.trace (ρ * CFC.log σ) -
        Matrix.trace (binaryPinching P ρ * CFC.log σ) = 0 := by
      simpa [Matrix.sub_mul, Matrix.trace_sub] using horth2
    exact sub_eq_zero.mp h'
  rw [Matrix.mul_sub, Matrix.trace_sub, Matrix.mul_sub, Matrix.trace_sub,
    Matrix.mul_sub, Matrix.trace_sub]
  rw [horth1', horth2']
  noncomm_ring

end InfoGeometry.Modular.UmegakiBinaryPinchingDataProcessing

end noncomputable section
