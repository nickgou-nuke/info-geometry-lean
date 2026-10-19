/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/

import InfoGeometry.Clifford.Cl44Spinors
import InfoGeometry.Algebra.FiniteSpinAlgebra
import Mathlib.LinearAlgebra.LinearIndependent.Basic

namespace InfoGeometry.Clifford.Cl44S3Family

/--
Data for a linear `S₃` action carrying a selected linearly independent
family to itself and commuting with two selected endomorphisms. This generic
structure does not by itself assert an action induced by the Clifford,
sedenion, or Albert algebra constructions, nor does it make the endomorphisms
representations of gauge groups.
-/
structure SplitS3FamilyDatum
    (V : Type*) [AddCommGroup V] [Module ℝ V] where
  s3Action : Equiv.Perm (Fin 3) → V →ₗ[ℝ] V
  action_one : s3Action 1 = LinearMap.id
  action_mul : ∀ σ τ,
    s3Action (σ * τ) = (s3Action σ).comp (s3Action τ)
  family : Fin 3 → V
  colorOperator : V →ₗ[ℝ] V
  chargeOperator : V →ₗ[ℝ] V
  preserves_semiSpinors : ∀ σ i,
    s3Action σ (family i) = family (σ i)
  color_invariant : ∀ σ,
    (s3Action σ).comp colorOperator = colorOperator.comp (s3Action σ)
  charge_invariant : ∀ σ,
    (s3Action σ).comp chargeOperator = chargeOperator.comp (s3Action σ)
  linearly_independent_families : LinearIndependent ℝ family

/-- The action is equivariant on the selected family. This does not assert
preservation of the full range of a semi-spinor projector. -/
def PreservesSemiSpinors {V : Type*} [AddCommGroup V] [Module ℝ V]
    (D : SplitS3FamilyDatum V) : Prop :=
  ∀ σ i, D.s3Action σ (D.family i) = D.family (σ i)

/-- The selected color endomorphism commutes with the family action. No
`SU(3)` representation is part of this predicate. -/
def ColorInvariant {V : Type*} [AddCommGroup V] [Module ℝ V]
    (D : SplitS3FamilyDatum V) : Prop :=
  ∀ σ, (D.s3Action σ).comp D.colorOperator =
    D.colorOperator.comp (D.s3Action σ)

/-- The selected charge endomorphism commutes with the family action. No
`U(1)` representation or charge spectrum is part of this predicate. -/
def ChargeInvariant {V : Type*} [AddCommGroup V] [Module ℝ V]
    (D : SplitS3FamilyDatum V) : Prop :=
  ∀ σ, (D.s3Action σ).comp D.chargeOperator =
    D.chargeOperator.comp (D.s3Action σ)

/-- The three generated families are linearly independent. -/
def LinearlyIndependentFamilies {V : Type*} [AddCommGroup V] [Module ℝ V]
    (D : SplitS3FamilyDatum V) : Prop :=
  LinearIndependent ℝ D.family

/--
Conditional readout of the properties stored in `SplitS3FamilyDatum`.
Existence of such a datum, and any physical interpretation as a
three-generation construction, require separate theorems.

-- DEBT_KIND: SORRY
-/
theorem splitCl44_three_generation_model
    {V : Type*} [AddCommGroup V] [Module ℝ V]
    (D : SplitS3FamilyDatum V) :
    PreservesSemiSpinors D ∧
    ColorInvariant D ∧
    ChargeInvariant D ∧
    LinearlyIndependentFamilies D := by
  exact ⟨D.preserves_semiSpinors, D.color_invariant,
    D.charge_invariant, D.linearly_independent_families⟩

/-- A finite real coordinate carrier witnessing that the generic datum can
be inhabited when the ambient module has room for a three-element family.
This is independent of the Cl(4,4) coordinate-submodule model. -/
abbrev CoordinateS3Carrier := Fin 3 → ℝ

/-- The permutation action on three real coordinates, by inverse
precomposition. -/
def coordinateS3Action (σ : Equiv.Perm (Fin 3)) :
    CoordinateS3Carrier →ₗ[ℝ] CoordinateS3Carrier where
  toFun x i := x (σ.symm i)
  map_add' x y := by
    funext i
    rfl
  map_smul' c x := by
    funext i
    rfl

/-- The coordinate basis family is permuted by `coordinateS3Action`. -/
def coordinateS3Family (i : Fin 3) : CoordinateS3Carrier :=
  fun j => if j = i then 1 else 0

theorem coordinateS3Action_one :
    coordinateS3Action (1 : Equiv.Perm (Fin 3)) = LinearMap.id := by
  apply LinearMap.ext
  intro x
  funext i
  change x ((Equiv.refl (Fin 3)).symm i) = x i
  rfl

theorem coordinateS3Action_mul (σ τ : Equiv.Perm (Fin 3)) :
    coordinateS3Action (σ * τ) =
      (coordinateS3Action σ).comp (coordinateS3Action τ) := by
  apply LinearMap.ext
  intro x
  funext i
  have hinv : (σ * τ).symm = τ.symm * σ.symm := by
    change (τ.trans σ).symm = τ.symm * σ.symm
    rw [Equiv.symm_trans]
    rfl
  change x ((σ * τ).symm i) = x (τ.symm (σ.symm i))
  rw [hinv]
  rfl

theorem coordinateS3Action_permutates_family
    (σ : Equiv.Perm (Fin 3)) (i : Fin 3) :
    coordinateS3Action σ (coordinateS3Family i) =
      coordinateS3Family (σ i) := by
  ext j
  have hiff : σ.symm j = i ↔ j = σ i := by
    constructor
    · intro h
      simpa using congrArg σ h
    · intro h
      simpa using congrArg (fun x => σ.symm x) h
  simp [coordinateS3Action, coordinateS3Family, hiff]

theorem coordinateS3Family_linearIndependent :
    LinearIndependent ℝ coordinateS3Family := by
  classical
  rw [linearIndependent_iff']
  intro s g hsum i his
  have hcoord :
      (∑ j ∈ s, g j * coordinateS3Family j i) = 0 := by
    simpa only [Pi.zero_apply, Finset.sum_apply, Pi.smul_apply, smul_eq_mul] using
      congrFun hsum i
  have hcollapse :
      (∑ j ∈ s, g j * coordinateS3Family j i) = g i := by
    rw [Finset.sum_eq_single i]
    · simp [coordinateS3Family]
    · intro j hj hji
      simp [coordinateS3Family, hji.symm]
    · intro hi
      exact (hi his).elim
  rw [hcollapse] at hcoord
  exact hcoord

/-- A concrete datum in a three-dimensional real coordinate module. The two
endomorphisms are identities; the fields do not encode gauge-group actions. -/
def coordinateS3Datum : SplitS3FamilyDatum CoordinateS3Carrier where
  s3Action := coordinateS3Action
  action_one := coordinateS3Action_one
  action_mul := coordinateS3Action_mul
  family := coordinateS3Family
  colorOperator := LinearMap.id
  chargeOperator := LinearMap.id
  preserves_semiSpinors := coordinateS3Action_permutates_family
  color_invariant := by intro σ; simp
  charge_invariant := by intro σ; simp
  linearly_independent_families := coordinateS3Family_linearIndependent

/-- Source-local constructive inhabitant for the generic family datum. -/
theorem coordinateS3Datum_nonempty :
    Nonempty (SplitS3FamilyDatum CoordinateS3Carrier) :=
  ⟨coordinateS3Datum⟩

end InfoGeometry.Clifford.Cl44S3Family
