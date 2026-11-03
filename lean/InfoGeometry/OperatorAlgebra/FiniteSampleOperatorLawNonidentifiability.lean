/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import Mathlib.Data.Matrix.Basic
import Mathlib.Tactic

/-!
# Finite observations do not identify an autonomous operator law

This module formalizes one precise mathematical lesson from inverse-law
reconstruction: agreement on finitely many operator states does not determine
a unique polynomial law on the whole operator algebra. The ambiguity is
exhibited inside a genuinely noncommutative matrix algebra, without restricting
to diagonal matrices or commuting operators.

This is an algebraic non-identifiability result. It does not select or claim to
recover any differential equation from a physical benchmark trajectory.
-/

namespace InfoGeometry.OperatorAlgebra.FiniteSampleOperatorLaw

variable {B : Type*} [Ring B]

/-- A polynomial perturbation vanishing at two observed operator states. -/
def sampleVanishingTerm (X₁ X₂ X : B) : B := (X - X₁) * (X - X₂)

/-- The perturbed candidate autonomous law. -/
def perturbedLaw (F : B → B) (X₁ X₂ X : B) : B :=
  F X + sampleVanishingTerm X₁ X₂ X

/-- The perturbed law agrees with the original law at the first sample. -/
theorem perturbedLaw_eq_at_first_sample (F : B → B) (X₁ X₂ : B) :
    perturbedLaw F X₁ X₂ X₁ = F X₁ := by
  unfold perturbedLaw sampleVanishingTerm
  noncomm_ring

/-- The perturbed law agrees with the original law at the second sample. -/
theorem perturbedLaw_eq_at_second_sample (F : B → B) (X₁ X₂ : B) :
    perturbedLaw F X₁ X₂ X₂ = F X₂ := by
  unfold perturbedLaw sampleVanishingTerm
  noncomm_ring

/-- Any third state where the ordered polynomial perturbation is nonzero
separates the two laws. No commutativity is assumed. -/
theorem perturbedLaw_ne_at_third_sample (F : B → B) (X₁ X₂ X₃ : B)
    (hNonzero : sampleVanishingTerm X₁ X₂ X₃ ≠ 0) :
    perturbedLaw F X₁ X₂ X₃ ≠ F X₃ := by
  intro hEq
  change F X₃ + sampleVanishingTerm X₁ X₂ X₃ = F X₃ at hEq
  have hZero : sampleVanishingTerm X₁ X₂ X₃ = 0 :=
    add_left_cancel (show F X₃ + sampleVanishingTerm X₁ X₂ X₃ = F X₃ + 0 by
      simpa using hEq)
  exact hNonzero hZero

/-! ## Explicit noncommutative matrix witness -/

abbrev Mat2 := Matrix (Fin 2) (Fin 2) ℂ

/-- First observed non-diagonal nilpotent matrix. -/
def sampleA : Mat2 := !![(0 : ℂ), 1; 0, 0]

/-- Second observed non-diagonal nilpotent matrix; it does not commute with
`sampleA`. -/
def sampleB : Mat2 := !![(0 : ℂ), 0; 1, 0]

/-- An unobserved non-diagonal matrix separating the two polynomial laws. -/
def sampleC : Mat2 := !![(1 : ℂ), 1; 1, 0]

/-- The observed matrices witness noncommutativity of the carrier. -/
theorem sampleA_sampleB_do_not_commute : sampleA * sampleB ≠ sampleB * sampleA := by
  intro h
  have h00 := congrArg (fun M : Mat2 => M 0 0) h
  norm_num [sampleA, sampleB, Matrix.mul_apply, Fin.sum_univ_two] at h00

/-- The two candidate laws agree at both supplied operator observations. -/
theorem two_sample_laws_agree_at_observations :
    perturbedLaw (fun _ : Mat2 => 0) sampleA sampleB sampleA = 0 ∧
    perturbedLaw (fun _ : Mat2 => 0) sampleA sampleB sampleB = 0 := by
  exact ⟨perturbedLaw_eq_at_first_sample _ _ _,
    perturbedLaw_eq_at_second_sample _ _ _⟩

/-- The candidate laws nevertheless differ at a third non-diagonal operator
state, proving that the two observations alone do not identify the law. -/
theorem two_sample_laws_disagree_off_sample :
    perturbedLaw (fun _ : Mat2 => 0) sampleA sampleB sampleC ≠ 0 := by
  have hNonzero : sampleVanishingTerm sampleA sampleB sampleC ≠ 0 := by
    intro h
    have h00 := congrArg (fun M : Mat2 => M 0 0) h
    norm_num [sampleVanishingTerm, sampleA, sampleB, sampleC,
      Matrix.sub_apply, Matrix.mul_apply, Fin.sum_univ_two] at h00
  exact perturbedLaw_ne_at_third_sample
    (fun _ : Mat2 => 0) sampleA sampleB sampleC hNonzero

/-! ## Causal dependency order -/

inductive IdentificationStage where
  | operatorCarrier
  | sampleConstraints
  | polynomialPerturbation
  | offSampleDisagreement
  deriving DecidableEq, Repr

/-- The finite-observation argument's reflexive-transitive causal order. -/
def IdentificationStage.dependencyLE : IdentificationStage → IdentificationStage → Prop
  | .operatorCarrier, _ => True
  | .sampleConstraints, .sampleConstraints => True
  | .sampleConstraints, .polynomialPerturbation => True
  | .sampleConstraints, .offSampleDisagreement => True
  | .polynomialPerturbation, .polynomialPerturbation => True
  | .polynomialPerturbation, .offSampleDisagreement => True
  | .offSampleDisagreement, .offSampleDisagreement => True
  | _, _ => False

theorem IdentificationStage.dependencyLE_refl (a : IdentificationStage) :
    a.dependencyLE a := by
  cases a <;> simp [dependencyLE]

theorem IdentificationStage.dependencyLE_trans {a b c : IdentificationStage}
    (hab : a.dependencyLE b) (hbc : b.dependencyLE c) : a.dependencyLE c := by
  cases a <;> cases b <;> cases c <;> simp_all [dependencyLE]

theorem IdentificationStage.dependencyLE_antisymm {a b : IdentificationStage}
    (hab : a.dependencyLE b) (hba : b.dependencyLE a) : a = b := by
  cases a <;> cases b <;> simp_all [dependencyLE]

instance : PartialOrder IdentificationStage where
  le := IdentificationStage.dependencyLE
  le_refl := IdentificationStage.dependencyLE_refl
  le_trans := fun _ _ _ hab hbc => IdentificationStage.dependencyLE_trans hab hbc
  le_antisymm := fun _ _ hab hba => IdentificationStage.dependencyLE_antisymm hab hba

/-- The archetypes form the causal chain: observations support a vanishing
perturbation, which yields a distinct law away from the observed states. -/
theorem inverse_problem_causal_dependencies :
    IdentificationStage.operatorCarrier ≤ IdentificationStage.sampleConstraints ∧
    IdentificationStage.sampleConstraints ≤ IdentificationStage.polynomialPerturbation ∧
    IdentificationStage.polynomialPerturbation ≤ IdentificationStage.offSampleDisagreement :=
  ⟨trivial, trivial, trivial⟩

end InfoGeometry.OperatorAlgebra.FiniteSampleOperatorLaw
