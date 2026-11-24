/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.Geometry.CotangentLieForm
import Mathlib.RepresentationTheory.Invariants

/-!
# Invariant covectors and cotangent forms for a finite real representation

Restriction identifies the invariant dual with the dual of the invariant
subspace. Its explicit inverse composes a covector with Mathlib's Reynolds
projection `Representation.averageMap`. The identification makes the
restricted cotangent form nondegenerate. Finite symmetry is a sufficient
condition; a separate shear counterexample records failure for an arbitrary
linear automorphism.
-/

noncomputable section

namespace InfoGeometry.Geometry.FiniteCotangentInvariants

open InfoGeometry.Clifford.NeutralPhaseSpaceCore
open InfoGeometry.Geometry.CotangentLieForm
open scoped BigOperators

section Linear

variable {G V : Type*} [Group G] [Fintype G] [AddCommGroup V] [Module ℝ V]

local instance cardInvertible : Invertible (Fintype.card G : ℝ) :=
  invertibleOfNonzero (by exact_mod_cast Fintype.card_ne_zero)

/-- The existing Reynolds average, with its codomain restricted to actual invariants. -/
def averagingProjection (ρ : Representation ℝ G V) : V →ₗ[ℝ] ρ.invariants :=
  ρ.averageMap.codRestrict ρ.invariants ρ.averageMap_invariant

@[simp] theorem averagingProjection_apply (ρ : Representation ℝ G V) (v : V) :
    (averagingProjection ρ v : V) = ρ.averageMap v := rfl

@[simp] theorem averagingProjection_fixed (ρ : Representation ℝ G V) (v : ρ.invariants) :
    averagingProjection ρ (v : V) = v := by
  apply Subtype.ext
  exact ρ.averageMap_id v v.property

/-- Reynolds averaging is also invariant under precomposition by the action. -/
theorem averagingProjection_action (ρ : Representation ℝ G V) (g : G) (v : V) :
    averagingProjection ρ (ρ g v) = averagingProjection ρ v := by
  apply Subtype.ext
  change (ρ.averageMap * ρ g) v = ρ.averageMap v
  have hm : ρ.averageMap * ρ g = ρ.averageMap := by
    rw [Representation.averageMap, ← Representation.asAlgebraHom_single_one,
      ← map_mul, GroupAlgebra.mul_average_right]
  rw [hm]

/-- Fixed covectors evaluate the same way before and after any group action. -/
theorem invariantDual_action (ρ : Representation ℝ G V)
    (α : ρ.dual.invariants) (g : G) (v : V) : α.1 (ρ g v) = α.1 v := by
  have h := congrArg (fun f : Module.Dual ℝ V => f v) (α.property g⁻¹)
  simpa [Representation.dual] using h

/-- Fixed covectors evaluate the same way before and after Reynolds projection. -/
theorem invariantDual_average (ρ : Representation ℝ G V)
    (α : ρ.dual.invariants) (v : V) : α.1 (ρ.averageMap v) = α.1 v := by
  simp [Representation.averageMap, GroupAlgebra.average, map_sum,
    invariantDual_action, Finset.card_univ, ← Nat.cast_smul_eq_nsmul ℝ,
    smul_smul]

/-- Extend a functional on the fixed subspace by averaging its argument. -/
def extendInvariantDual (ρ : Representation ℝ G V)
    (f : Module.Dual ℝ ρ.invariants) : ρ.dual.invariants :=
  ⟨f.comp (averagingProjection ρ), by
    intro g
    apply LinearMap.ext
    intro v
    change f (averagingProjection ρ (ρ g⁻¹ v)) = f (averagingProjection ρ v)
    rw [averagingProjection_action]⟩

/-- The actual restriction/extension equivalence `(V*)ᴳ ≃ (Vᴳ)*`. -/
def invariantDualEquiv (ρ : Representation ℝ G V) :
    ρ.dual.invariants ≃ₗ[ℝ] Module.Dual ℝ ρ.invariants where
  toFun α := α.1.comp ρ.invariants.subtype
  invFun := extendInvariantDual ρ
  left_inv α := by
    apply Subtype.ext
    apply LinearMap.ext
    intro v
    exact invariantDual_average ρ α v
  right_inv f := by
    apply LinearMap.ext
    intro v
    change f (averagingProjection ρ (v : V)) = f v
    rw [averagingProjection_fixed]
  map_add' := by intros; rfl
  map_smul' := by intros; rfl

@[simp] theorem invariantDualEquiv_apply (ρ : Representation ℝ G V)
    (α : ρ.dual.invariants) (v : ρ.invariants) : invariantDualEquiv ρ α v = α.1 v := rfl

@[simp] theorem invariantDualEquiv_symm_apply (ρ : Representation ℝ G V)
    (f : Module.Dual ℝ ρ.invariants) (v : V) :
    ((invariantDualEquiv ρ).symm f).1 v = f (averagingProjection ρ v) := rfl

/-- Inclusion of the actual fixed primal and dual spaces into the ambient phase space. -/
def fixedPhaseInclusion (ρ : Representation ℝ G V) :
    (ρ.invariants × ρ.dual.invariants) →ₗ[ℝ] PhaseSpaceCarrier V :=
  ρ.invariants.subtype.prodMap ρ.dual.invariants.subtype

/-- Fixed primal/dual pairs are canonically the cotangent space of the invariant space. -/
def fixedCotangentEquiv (ρ : Representation ℝ G V) :
    (ρ.invariants × ρ.dual.invariants) ≃ₗ[ℝ] PhaseSpaceCarrier ρ.invariants :=
  (LinearEquiv.refl ℝ ρ.invariants).prodCongr (invariantDualEquiv ρ)

/-- The restricted form is the pullback of the existing canonical form on the fixed space. -/
theorem fixedCotangentEquiv_omega (ρ : Representation ℝ G V)
    (z w : ρ.invariants × ρ.dual.invariants) :
    neutralOmega (fixedPhaseInclusion ρ z) (fixedPhaseInclusion ρ w) =
      neutralOmega (fixedCotangentEquiv ρ z) (fixedCotangentEquiv ρ w) := by
  rfl

/-- The actual restriction of the ambient canonical form to fixed primal/dual pairs. -/
def fixedCotangentForm (ρ : Representation ℝ G V) :
    LinearMap.BilinForm ℝ (ρ.invariants × ρ.dual.invariants) :=
  (neutralOmega (E := V)).compl₁₂ (fixedPhaseInclusion ρ) (fixedPhaseInclusion ρ)

theorem fixedCotangentForm_isAlt (ρ : Representation ℝ G V) :
    (fixedCotangentForm ρ).IsAlt := by
  intro z
  change neutralOmega (fixedPhaseInclusion ρ z) (fixedPhaseInclusion ρ z) = 0
  simp

/-- Finite symmetry prevents degeneration of the fixed cotangent form. -/
theorem fixedCotangentForm_nondegenerate (ρ : Representation ℝ G V) :
    (fixedCotangentForm ρ).Nondegenerate := by
  constructor
  · intro z hz
    apply (fixedCotangentEquiv ρ).injective
    rw [map_zero]
    apply (neutralOmega_nondegenerate (E := ρ.invariants)).1
    intro w
    obtain ⟨w, rfl⟩ := (fixedCotangentEquiv ρ).surjective w
    rw [← fixedCotangentEquiv_omega]
    exact hz w
  · intro z hz
    apply (fixedCotangentEquiv ρ).injective
    rw [map_zero]
    apply (neutralOmega_nondegenerate (E := ρ.invariants)).2
    intro w
    obtain ⟨w, rfl⟩ := (fixedCotangentEquiv ρ).surjective w
    rw [← fixedCotangentEquiv_omega]
    exact hz w

end Linear

section Lie

variable {G V : Type*} [Group G] [Fintype G] [LieRing V] [LieAlgebra ℝ V]

/-- The bracket-corrected ambient form restricted to the actual fixed factors. -/
def fixedCotangentLieForm (ρ : Representation ℝ G V) (α : Module.Dual ℝ V) :
    LinearMap.BilinForm ℝ (ρ.invariants × ρ.dual.invariants) :=
  (cotangentForm α).compl₁₂ (fixedPhaseInclusion ρ) (fixedPhaseInclusion ρ)

theorem fixedCotangentLieForm_isAlt (ρ : Representation ℝ G V)
    (α : Module.Dual ℝ V) : (fixedCotangentLieForm ρ α).IsAlt := by
  intro z
  exact cotangentForm_isAlt α (fixedPhaseInclusion ρ z)

/-- The fixed-factor bracket correction still has no radical. -/
theorem fixedCotangentLieForm_nondegenerate (ρ : Representation ℝ G V)
    (α : Module.Dual ℝ V) : (fixedCotangentLieForm ρ α).Nondegenerate := by
  have hleft : (fixedCotangentLieForm ρ α).SeparatingLeft := by
    intro z hz
    have hx : z.1 = 0 := by
      apply (Module.forall_dual_apply_eq_zero_iff ℝ z.1).mp
      intro β
      have h := hz (0, (invariantDualEquiv ρ).symm β)
      change cotangentForm α (z.1.1, z.2.1) (0, ((invariantDualEquiv ρ).symm β).1) = 0 at h
      simpa using h
    have hp : z.2 = 0 := by
      apply (invariantDualEquiv ρ).injective
      apply LinearMap.ext
      intro y
      have h := hz (y, 0)
      change cotangentForm α (z.1.1, z.2.1) (y.1, 0) = 0 at h
      simpa [hx] using h
    exact Prod.ext hx hp
  refine ⟨hleft, ?_⟩
  intro z hz
  apply hleft z
  intro w
  change cotangentForm α (fixedPhaseInclusion ρ z) (fixedPhaseInclusion ρ w) = 0
  rw [cotangentForm_skew]
  exact neg_eq_zero.mpr (hz w)

end Lie

end InfoGeometry.Geometry.FiniteCotangentInvariants
