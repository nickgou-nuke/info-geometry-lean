/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import Mathlib.Tactic
import InfoGeometry.Algebra.FiniteSpinAlgebra
import InfoGeometry.SuperGrassmannian.RealMajoranaChiralIdeal

/-!
# Section 82 Audit: Real Majorana Substrate, Chiral Ideals, Spinor Bilinears, and Fierz Identities

Module: `InfoGeometry.SuperGrassmannian.RealMajoranaChiralIdealAudit`

Independent Gate 2 Adversarial and Gate 4 Acceptance QA suite for Section 82.
Confirms:
- Zero sorry, zero admit, zero custom axioms.
- Strict kernel verification of the individual component theorems.
- Non-vacuous concrete witnesses on `ℝ`.
-/

namespace InfoGeometry.SuperGrassmannian.RealMajoranaChiralIdealAudit

open InfoGeometry.SuperGrassmannian.RealMajoranaChiralIdeal

/-- Explicit T16 non-commutativity witness on `Matrix (Fin 2) (Fin 2) ℝ`. -/
theorem audit_real_majorana_noncomm_witness :
    ∃ A B : Matrix (Fin 2) (Fin 2) ℝ, A * B ≠ B * A := by
  refine ⟨matGamma, matJ, fun h => ?_⟩
  have h01 := congrFun (congrFun h 0) 1
  norm_num [matGamma, matJ, Matrix.mul_apply, Fin.sum_univ_two] at h01

/-- Audit 1: Direct conjunction of the proved component theorems, with no certificate bundle. -/
theorem audit_real_majorana_chiral_ideal_components :
    (∀ (R : Type) [Ring R] (S : ChiralSheetSubstrate R), S.PL + S.PR = 1) ∧
    (∀ (R : Type) [Ring R] (S : ChiralSheetSubstrate R), S.PL * S.PR = 0 ∧ S.PR * S.PL = 0) ∧
    (∀ (R : Type) [Ring R] (S : ChiralSheetSubstrate R), S.J * S.PL * S.J = S.PR ∧ S.J * S.PR * S.J = S.PL) ∧
    (∀ (R : Type) [Ring R] (S : ChiralSheetSubstrate R), S.K ^ 2 = -1) ∧
    (∀ (R : Type) [Ring R] (S : ChiralSheetSubstrate R) (γ : R),
      S.superchargeQ γ ^ 2 = 0 ∧ S.superchargeQ_dag γ ^ 2 = 0) ∧
    (∀ (R : Type) [Ring R] (S : ChiralSheetSubstrate R) (γ : R),
      S.susyH γ * S.superchargeQ γ - S.superchargeQ γ * S.susyH γ = 0) ∧
    (∀ (R : Type) [Ring R] (ψ φ : Fin 2 → R),
      (2 : R) • dyad ψ φ =
        bilinScalar ψ φ • matOne + bilinChiral ψ φ • matGamma +
        bilinVector1 ψ φ • matJ - bilinVector2 ψ φ • matK) ∧
    (∀ (R : Type) [Ring R],
      kronMul (matPL (R := R)) matPL + kronMul matPR matPR +
      kronMul matQ matQ_dag + kronMul matQ_dag matQ = Swap2) ∧
    (∀ (R : Type) [Ring R],
      (2 : R) • (Swap2 (R := R)) =
        kronMul (matOne (R := R)) matOne + kronMul matGamma matGamma +
        kronMul matJ matJ - kronMul matK matK) ∧
    (∀ (R : Type) [Ring R] (X : Matrix (Fin 2) (Fin 2) R),
      gradingDeriv (gradingDeriv (gradingDeriv X)) = (4 : R) • gradingDeriv X) ∧
    (∀ (R : Type) [Ring R] (v : R), superTrace2 (matSusyH (R := R) v) = 0) := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intros R _ S; exact S.PL_add_PR
  · intros R _ S; exact ⟨S.PL_mul_PR, S.PR_mul_PL⟩
  · intros R _ S; exact ⟨S.J_PL_J, S.J_PR_J⟩
  · intros R _ S; exact S.K_sq
  · intros R _ S γ; exact ⟨S.Q_sq γ, S.Q_dag_sq γ⟩
  · intros R _ S γ; exact S.susyH_comm_Q γ
  · intros R _ ψ φ; exact real_spinor_dyadic_expansion ψ φ
  · intros R _; exact real_chiral_fierz_ideal_identity
  · intros R _; exact real_chiral_fierz_pauli_identity
  · intros R _ X; exact grading_derivation_cube X
  · intros R _ v; exact superTrace2_susyH v

/-- Audit 2: Concrete non-vacuity witness of the 2-sheeted chiral substrate over M₂(ℝ). -/
noncomputable def realSubstrateWitness : ChiralSheetSubstrate (Matrix (Fin 2) (Fin 2) ℝ) where
  Γ := matGamma
  J := matJ
  Γ_sq := by rw [sq]; exact matGamma_sq
  J_sq := by rw [sq]; exact matJ_sq
  J_Γ_anticomm := matJ_matGamma_anticomm
  half := (1 / 2 : ℝ) • (1 : Matrix (Fin 2) (Fin 2) ℝ)
  two_half := by
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [Matrix.smul_apply, Matrix.add_apply] <;>
      norm_num
  half_comm := fun X => by
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [Matrix.mul_apply, Matrix.smul_apply, Matrix.one_apply] <;>
      ring

theorem audit_nonvacuous_real_substrate :
    realSubstrateWitness.PL + realSubstrateWitness.PR = 1 :=
  realSubstrateWitness.PL_add_PR

/-- Audit 3: Concrete non-vacuity of the Dyadic Outer Product Theorem on real vectors. -/
theorem audit_nonvacuous_dyadic_expansion :
    let ψ : Fin 2 → ℝ := ![1, 2]
    let φ : Fin 2 → ℝ := ![3, 4]
    (2 : ℝ) • dyad ψ φ =
      bilinScalar ψ φ • matOne +
      bilinChiral ψ φ • matGamma +
      bilinVector1 ψ φ • matJ -
      bilinVector2 ψ φ • matK :=
  real_spinor_dyadic_expansion ![1, 2] ![3, 4]

/-- Audit 4: Concrete non-vacuity of the Real Chiral Fierz Ideal Identity. -/
theorem audit_nonvacuous_fierz_ideal :
    kronMul (matPL (R := ℝ)) matPL +
    kronMul matPR matPR +
    kronMul matQ matQ_dag +
    kronMul matQ_dag matQ = Swap2 :=
  real_chiral_fierz_ideal_identity

/-- Audit 5: Concrete non-vacuity of the Real SUSY Vacuum Energy Cancellation. -/
theorem audit_nonvacuous_vacuum_energy (v : ℝ) :
    superTrace2 (matSusyH (R := ℝ) v) = 0 :=
  superTrace2_susyH v

end InfoGeometry.SuperGrassmannian.RealMajoranaChiralIdealAudit
