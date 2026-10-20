/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.Topology.KleinRealOperatorDescent

/-!
# Anticommuting operator descent on the Klein orbit quotient

The quotient owner already descends individual glide-invariant-preserving
operators and proves square-zero transport.  This closure transports the
cross-term anticommutation law itself, which is the algebraic condition needed
for a descended Dirac-Hodge operator to retain its chiral odd/even split.
-/

noncomputable section

namespace InfoGeometry.Topology.KleinRealOperatorDescent

open KleinBrillouinBase KleinBottleOrbitQuotient

variable {V : Type*} [AddCommGroup V] [Module ℝ V]

private theorem restrictOperator_mul
    (operator₁ operator₂ : Module.End ℝ (BrillouinTorus → V))
    (preserves₁ preserves₂ : ∀ field : invariantFields (V := V),
      _ ) :
    restrictOperator operator₁ preserves₁ * restrictOperator operator₂ preserves₂ =
      restrictOperator (operator₁ * operator₂) (by
        intro field
        exact preserves₁ ⟨operator₂ field, preserves₂ field⟩) := by
  apply LinearMap.ext
  intro field
  apply Subtype.ext
  rfl

theorem quotientOperator_anticommutes
    (operator₁ operator₂ : Module.End ℝ (BrillouinTorus → V))
    (preserves₁ preserves₂ : ∀ field : invariantFields (V := V),
      operator₁ field ∈ invariantFields ∧ operator₂ field ∈ invariantFields)
    (hanticomm : operator₁ * operator₂ = -(operator₂ * operator₁)) :
    quotientOperator operator₁ (fun field => (preserves₁ field).1) *
        quotientOperator operator₂ (fun field => (preserves₂ field).2) =
      -(quotientOperator operator₂ (fun field => (preserves₂ field).2) *
        quotientOperator operator₁ (fun field => (preserves₁ field).1)) := by
  have h12 : restrictOperator operator₁ (fun field => (preserves₁ field).1) *
        restrictOperator operator₂ (fun field => (preserves₂ field).2) =
      restrictOperator (operator₁ * operator₂) (by
        intro field
        exact (preserves₁ ⟨operator₂ field, (preserves₂ field).2⟩).1) := by
    exact restrictOperator_mul operator₁ operator₂
      (fun field => (preserves₁ field).1)
      (fun field => (preserves₂ field).2)
  have h21 : restrictOperator operator₂ (fun field => (preserves₂ field).2) *
        restrictOperator operator₁ (fun field => (preserves₁ field).1) =
      restrictOperator (operator₂ * operator₁) (by
        intro field
        exact (preserves₂ ⟨operator₁ field, (preserves₁ field).1⟩).2) := by
    exact restrictOperator_mul operator₂ operator₁
      (fun field => (preserves₂ field).2)
      (fun field => (preserves₁ field).1)
  have hcomp :
      restrictOperator (operator₁ * operator₂) (by
        intro field
        exact (preserves₁ ⟨operator₂ field, (preserves₂ field).2⟩).1) =
        restrictOperator (-(operator₂ * operator₁)) (by
          intro field
          simpa using (preserves₂ ⟨operator₁ field, (preserves₁ field).1⟩).2) := by
    apply LinearMap.ext
    intro field
    apply Subtype.ext
    exact congrArg (fun op => op (field : BrillouinTorus → V)) hanticomm
  have hrestrict :
      restrictOperator operator₁ (fun field => (preserves₁ field).1) *
        restrictOperator operator₂ (fun field => (preserves₂ field).2) =
      -(restrictOperator operator₂ (fun field => (preserves₂ field).2) *
        restrictOperator operator₁ (fun field => (preserves₁ field).1)) := by
    calc
      _ = restrictOperator (operator₁ * operator₂) (by
        intro field
        exact (preserves₁ ⟨operator₂ field, (preserves₂ field).2⟩).1) := h12
      _ = restrictOperator (-(operator₂ * operator₁)) (by
        intro field
        simpa using (preserves₂ ⟨operator₁ field, (preserves₁ field).1⟩).2) := hcomp
      _ = -(restrictOperator (operator₂ * operator₁) (by
        intro field
        exact (preserves₂ ⟨operator₁ field, (preserves₁ field).1⟩).2)) := by
        apply LinearMap.ext
        intro field
        apply Subtype.ext
        rfl
      _ = _ := congrArg Neg.neg h21.symm
  unfold quotientOperator
  rw [← map_mul, ← map_mul]
  calc
    _ = (LinearEquiv.conjAlgEquiv ℝ (fieldEquiv (V := V)).symm)
        (-(restrictOperator operator₂ (fun field => (preserves₂ field).2) *
          restrictOperator operator₁ (fun field => (preserves₁ field).1))) :=
      congrArg (LinearEquiv.conjAlgEquiv ℝ (fieldEquiv (V := V)).symm) hrestrict
    _ = -(LinearEquiv.conjAlgEquiv ℝ (fieldEquiv (V := V)).symm)
        (restrictOperator operator₂ (fun field => (preserves₂ field).2) *
          restrictOperator operator₁ (fun field => (preserves₁ field).1)) :=
      map_neg (LinearEquiv.conjAlgEquiv ℝ (fieldEquiv (V := V)).symm) _
    _ = _ := by rw [map_mul]

end InfoGeometry.Topology.KleinRealOperatorDescent
