/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import Mathlib.GroupTheory.GroupAction.FixingSubgroup
import Mathlib.GroupTheory.GroupAction.Quotient
import Mathlib.GroupTheory.Subgroup.Centralizer

/-!
# Conjugation of group-valued motions and their exact symmetry subgroups

Postcomposition with the native inner automorphism `MulAut.conj g` acts on
monoid homomorphisms `T →* G`. Its stabilizer is exactly the centralizer of
the image. Pointwise symmetry of a family likewise centralizes all its
time values, equivalently the subgroup they generate.

The action is a named reducible non-instance: consumers choose this action
explicitly with `letI := flowConjugationAction T G`. No global action on
every homomorphism type is installed.

This owner is algebraic. Specialization to `T = Multiplicative ℝ` does not
by itself assert time continuity, differentiability or an ODE existence
theorem; those hypotheses belong to the analytic flow owner.
-/

namespace InfoGeometry.Canonical.FlowConjugation

variable (T G : Type*) [Monoid T] [Group G]

/-- Conjugate every time value by the same native inner automorphism. -/
abbrev flowConjugationAction : MulAction G (T →* G) where
  smul g Φ := (MulAut.conj g).toMonoidHom.comp Φ
  one_smul Φ := by
    ext t
    change (1 : G) * Φ t * (1 : G)⁻¹ = Φ t
    simp
  mul_smul g h Φ := by
    ext t
    change (g * h) * Φ t * (g * h)⁻¹ = g * (h * Φ t * h⁻¹) * g⁻¹
    simp [mul_assoc]

attribute [local instance] flowConjugationAction

variable {T G}

@[simp] theorem conjugate_flow_apply (g : G) (Φ : T →* G) (t : T) :
    (g • Φ) t = g * Φ t * g⁻¹ := rfl

/-- Pointwise invariance means commuting with every time value, with the
time parameter unchanged. -/
theorem conjugate_flow_eq_self_iff (g : G) (Φ : T →* G) :
    g • Φ = Φ ↔ ∀ t, g * Φ t = Φ t * g := by
  constructor
  · intro h t
    have ht := DFunLike.congr_fun h t
    change g * Φ t * g⁻¹ = Φ t at ht
    exact mul_inv_eq_iff_eq_mul.mp ht
  · intro h
    ext t
    change g * Φ t * g⁻¹ = Φ t
    exact mul_inv_eq_iff_eq_mul.mpr (h t)

theorem mem_flow_stabilizer_iff (g : G) (Φ : T →* G) :
    g ∈ MulAction.stabilizer G Φ ↔ ∀ t, g * Φ t = Φ t * g := by
  rw [MulAction.mem_stabilizer_iff, conjugate_flow_eq_self_iff]

/-- The symmetry subgroup of a motion is the native centralizer of its
image, not the normalizer of that image. -/
theorem flow_stabilizer_eq_centralizer (Φ : T →* G) :
    MulAction.stabilizer G Φ = Subgroup.centralizer (Set.range Φ) := by
  ext g
  rw [mem_flow_stabilizer_iff, Subgroup.mem_centralizer_iff]
  constructor
  · intro h y hy
    rcases hy with ⟨t, rfl⟩
    exact (h t).symm
  · intro h t
    exact (h (Φ t) ⟨t, rfl⟩).symm

/-- Common pointwise symmetry is exactly commutation with all time values
of every selected motion. -/
theorem mem_fixing_flows_iff (S : Set (T →* G)) (g : G) :
    g ∈ fixingSubgroup G S ↔ ∀ Φ ∈ S, ∀ t, g * Φ t = Φ t * g := by
  simp only [mem_fixingSubgroup_iff, conjugate_flow_eq_self_iff]

/-- Pointwise symmetry of a family is the centralizer of the union of its
images. No setwise invariance or reparametrization is asserted. -/
theorem fixing_flows_eq_centralizer (S : Set (T →* G)) :
    fixingSubgroup G S = Subgroup.centralizer (⋃ Φ ∈ S, Set.range Φ) := by
  ext g
  rw [mem_fixing_flows_iff, Subgroup.mem_centralizer_iff]
  constructor
  · intro h y hy
    rcases Set.mem_iUnion.mp hy with ⟨Φ, hy⟩
    rcases Set.mem_iUnion.mp hy with ⟨hΦ, hy⟩
    rcases hy with ⟨t, rfl⟩
    exact (h Φ hΦ t).symm
  · intro h Φ hΦ t
    exact (h (Φ t) (Set.mem_iUnion.mpr
      ⟨Φ, Set.mem_iUnion.mpr ⟨hΦ, ⟨t, rfl⟩⟩⟩)).symm

/-- Passing from the union of flow images to its generated subgroup does
not change the common centralizer. -/
theorem fixing_flows_eq_centralizer_generated (S : Set (T →* G)) :
    fixingSubgroup G S =
      Subgroup.centralizer
        (Subgroup.closure (⋃ Φ ∈ S, Set.range Φ) : Set G) := by
  rw [Subgroup.centralizer_closure, fixing_flows_eq_centralizer]

/-- Transporting the motion transports its centralizer by the same inner
automorphism, using Mathlib's stabilizer conjugacy theorem. -/
theorem conjugate_flow_centralizer (g : G) (Φ : T →* G) :
    Subgroup.centralizer (Set.range (g • Φ)) =
      (Subgroup.centralizer (Set.range Φ)).map (MulAut.conj g).toMonoidHom := by
  simpa only [flow_stabilizer_eq_centralizer] using
    (MulAction.stabilizer_smul_eq_stabilizer_map_conj g Φ)

/-- The actual orbit of a group-valued motion is the native coset space by
its centralizer. This is an equivalence of types, with no quotient-manifold
or transitivity-on-all-motions assertion. -/
noncomputable def flowOrbitEquivCentralizerQuotient (Φ : T →* G) :
    MulAction.orbit G Φ ≃ G ⧸ Subgroup.centralizer (Set.range Φ) := by
  rw [← flow_stabilizer_eq_centralizer]
  exact MulAction.orbitEquivQuotientStabilizer G Φ

end InfoGeometry.Canonical.FlowConjugation
