/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/

import Mathlib.Tactic
import InfoGeometry.Algebra.FiniteSpinAlgebra

/-!
# Real Majorana matrix carrier

This recovered file keeps the explicit `4 × 4` real matrices and separates the
algebraic identities they are intended to satisfy from proved theorems.  The
former unproved chiral/Cuntz/topological claims are now statement shapes.
-/

namespace InfoGeometry.MajoranaTensorBridge

open Matrix

/-- Four-by-four real matrices. -/
abbrev MajoranaMatrix : Type := Matrix (Fin 4) (Fin 4) ℝ

/-- `γ⁰` in a real Majorana-style representation. -/
def gamma0_maj : MajoranaMatrix :=
  !![ 1,  0,  0,  0;
      0,  1,  0,  0;
      0,  0, -1,  0;
      0,  0,  0, -1]

/-- `γ¹` in a real Majorana-style representation. -/
def gamma1_maj : MajoranaMatrix :=
  !![ 0,  0,  1,  0;
      0,  0,  0,  1;
      1,  0,  0,  0;
      0,  1,  0,  0]

/-- The first two Majorana generators anticommute. -/
theorem gamma0_gamma1_anticommutator_zero :
    gamma0_maj * gamma1_maj + gamma1_maj * gamma0_maj = 0 := by
  ext i j <;> fin_cases i <;> fin_cases j <;>
    simp [gamma0_maj, gamma1_maj, Matrix.mul_apply, Fin.sum_univ_four]

/-- The displayed Majorana generators are genuinely noncommutative. -/
theorem gamma0_mul_gamma1_ne_gamma1_mul_gamma0 :
    (gamma0_maj * gamma1_maj : Matrix (Fin 4) (Fin 4) ℝ) ≠
      gamma1_maj * gamma0_maj := by
  intro h
  have h' := congrArg (fun M => M 0 2) h
  simp [gamma0_maj, gamma1_maj, Matrix.mul_apply, Fin.sum_univ_four] at h'
  norm_num at h'

/-- `γ²` in a real Majorana-style representation. -/
def gamma2_maj : MajoranaMatrix :=
  !![ 0,  0,  0,  1;
      0,  0,  1,  0;
      0, -1,  0,  0;
     -1,  0,  0,  0]

/-- `γ³` in a real Majorana-style representation. -/
def gamma3_maj : MajoranaMatrix :=
  !![ 0,  0,  1,  0;
      0,  0,  0, -1;
     -1,  0,  0,  0;
      0,  1,  0,  0]

/-- The displayed Majorana matrices have signature `(2,2)`. -/
theorem majoranaSignatureSquares :
  gamma0_maj * gamma0_maj = 1 ∧
  gamma1_maj * gamma1_maj = 1 ∧
  gamma2_maj * gamma2_maj = -1 ∧
  gamma3_maj * gamma3_maj = -1 := by
  constructor
  · ext i j <;> fin_cases i <;> fin_cases j <;>
      simp [gamma0_maj, Matrix.mul_apply, Fin.sum_univ_four]
  constructor
  · ext i j <;> fin_cases i <;> fin_cases j <;>
      simp [gamma1_maj, Matrix.mul_apply, Fin.sum_univ_four]
  constructor
  · ext i j <;> fin_cases i <;> fin_cases j <;>
      simp [gamma2_maj, Matrix.mul_apply, Fin.sum_univ_four]
  · ext i j <;> fin_cases i <;> fin_cases j <;>
      simp [gamma3_maj, Matrix.mul_apply, Fin.sum_univ_four]

/-- The mixed commutator `Σᵘᵛ = [γᵘ, γᵛ]`. -/
noncomputable def realLorentzGenerator (gamma_u gamma_v : MajoranaMatrix) : MajoranaMatrix :=
  gamma_u * gamma_v - gamma_v * gamma_u

/-- A spacetime vector embedded into the matrix span of the four generators. -/
noncomputable def majoranaSpacetimeVector (t x y z : ℝ) : MajoranaMatrix :=
  t • gamma0_maj + x • gamma1_maj + y • gamma2_maj + z • gamma3_maj

/-- Pure associativity fact for conjugation by an inverse matrix. -/
theorem majorana_lorentz_sandwich (S V S_inv : MajoranaMatrix)
    (_h_inv : S * S_inv = 1) (h_inv2 : S_inv * S = 1) :
    (S * V * S_inv) * (S * V * S_inv) = S * (V * V) * S_inv := by
  calc
    (S * V * S_inv) * (S * V * S_inv)
        = S * V * (S_inv * S) * V * S_inv := by simp only [Matrix.mul_assoc]
    _ = S * V * 1 * V * S_inv := by rw [h_inv2]
    _ = S * V * V * S_inv := by simp only [Matrix.mul_one]
    _ = S * (V * V) * S_inv := by simp only [Matrix.mul_assoc]

/-- Candidate chiral volume element. -/
noncomputable def gamma5_maj : MajoranaMatrix :=
  gamma0_maj * gamma1_maj * gamma2_maj * gamma3_maj

/-- The candidate chiral volume element is an involution. -/
theorem gamma5_maj_sq : gamma5_maj * gamma5_maj = 1 := by
  ext i j <;> fin_cases i <;> fin_cases j <;>
    simp [gamma5_maj, gamma0_maj, gamma1_maj, gamma2_maj, gamma3_maj,
      Matrix.mul_apply, Fin.sum_univ_four] <;> ring

/-- Candidate chiral projectors. -/
noncomputable def chiralProjectorL : MajoranaMatrix := (1 / 2 : ℝ) • (1 - gamma5_maj)
noncomputable def chiralProjectorR : MajoranaMatrix := (1 / 2 : ℝ) • (1 + gamma5_maj)

/-- Chiral supertrace expression. -/
noncomputable def chiralSupertrace (A : MajoranaMatrix) : ℝ := Matrix.trace (gamma5_maj * A)

/-- The chiral grading has zero trace. -/
theorem gamma5_maj_trace_zero : Matrix.trace gamma5_maj = 0 := by
  simp [gamma5_maj, gamma0_maj, gamma1_maj, gamma2_maj, gamma3_maj,
    Matrix.trace, Matrix.mul_apply, Fin.sum_univ_four]

/-- The basic chiral trace identities. -/
theorem chiralTraceIdentities :
  chiralSupertrace 1 = 0 ∧
  Matrix.trace chiralProjectorL = 2 ∧
  Matrix.trace chiralProjectorR = 2 := by
  unfold chiralSupertrace chiralProjectorL chiralProjectorR
  constructor
  · simpa [Matrix.mul_one] using gamma5_maj_trace_zero
  constructor
  · rw [Matrix.trace_smul, Matrix.trace_sub]
    simp [gamma5_maj_trace_zero]
    norm_num
  · rw [Matrix.trace_smul, Matrix.trace_add]
    simp [gamma5_maj_trace_zero]
    norm_num

/-- Candidate nilpotent generator. -/
noncomputable def cuntzGeneratorPlus : MajoranaMatrix := (1 / 2 : ℝ) • (gamma0_maj + gamma2_maj)

/-- Candidate parity-conjugate nilpotent generator. -/
noncomputable def cuntzGeneratorMinus : MajoranaMatrix := (1 / 2 : ℝ) • (gamma0_maj - gamma2_maj)

/-- The two null generators are nilpotent and form a complementary pair. -/
theorem cuntzGeneratorIdentities :
  cuntzGeneratorPlus * cuntzGeneratorPlus = 0 ∧
  cuntzGeneratorMinus * cuntzGeneratorMinus = 0 ∧
  cuntzGeneratorPlus * cuntzGeneratorMinus + cuntzGeneratorMinus * cuntzGeneratorPlus = 1 := by
  constructor
  · ext i j <;> fin_cases i <;> fin_cases j <;>
      simp [cuntzGeneratorPlus, gamma0_maj, gamma2_maj, Matrix.mul_apply,
        Fin.sum_univ_four] <;> ring
  constructor
  · ext i j <;> fin_cases i <;> fin_cases j <;>
      simp [cuntzGeneratorMinus, gamma0_maj, gamma2_maj, Matrix.mul_apply,
        Fin.sum_univ_four] <;> ring
  · ext i j <;> fin_cases i <;> fin_cases j <;>
      simp [cuntzGeneratorPlus, cuntzGeneratorMinus, gamma0_maj, gamma2_maj,
        Matrix.mul_apply, Fin.sum_univ_four] <;> ring

end InfoGeometry.MajoranaTensorBridge
