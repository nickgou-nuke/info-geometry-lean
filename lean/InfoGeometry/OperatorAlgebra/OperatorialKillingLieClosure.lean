/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.Algebra.NonAssocDerivation
import Mathlib.Algebra.Lie.SkewAdjoint
import Mathlib.Basic.Real.Basic

/-!
# Killing derivations of a noncommutative real algebra

The existing `NonAssocDerivation.derivations` owner is the native Lie
subalgebra of `Module.End` satisfying the actual Leibniz identity. Unlike
Mathlib's `Derivation`, it does not require commutative multiplication.

We intersect this owner with endomorphisms annihilated by a linear functional
and with Mathlib's `skewAdjointLieSubalgebra` for a bilinear form. The native
Lie-span universal property then proves closure under arbitrary finite Lie
expressions and real linear combinations.

The functional is not assumed positive or normalized, and the bilinear form
is not assumed positive, symmetric, or nondegenerate. Such assumptions may
be supplied by a particular state/metric owner, but are unnecessary for this
closure theorem. No exponentiation, boundedness, automorphism integration,
complete positivity, Koopman identification, or modular-flow claim follows
from the algebraic closure theorem alone.
-/

noncomputable section

namespace InfoGeometry.OperatorAlgebra

attribute [local instance 100] LieRing.ofAssociativeRing

section LinearFunctional

variable {V : Type*} [AddCommGroup V] [Module ℝ V]

/-- Endomorphisms whose outputs lie in the kernel of a chosen functional.
They form a genuine commutator Lie subalgebra. -/
def functionalAnnihilatingLieSubalgebra (ω : V →ₗ[ℝ] ℝ) :
    LieSubalgebra ℝ (Module.End ℝ V) where
  carrier := {D | ∀ x : V, ω (D x) = 0}
  zero_mem' := by
    intro x
    simp
  add_mem' := by
    intro D E hD hE x
    change ω (D x + E x) = 0
    rw [map_add, hD, hE, add_zero]
  smul_mem' := by
    intro r D hD x
    change ω (r • D x) = 0
    rw [map_smul, hD, smul_zero]
  lie_mem' := by
    intro D E hD hE x
    change ω (D (E x) - E (D x)) = 0
    rw [map_sub, hD, hE, sub_self]

@[simp] theorem mem_functionalAnnihilatingLieSubalgebra
    (ω : V →ₗ[ℝ] ℝ) (D : Module.End ℝ V) :
    D ∈ functionalAnnihilatingLieSubalgebra ω ↔ ∀ x : V, ω (D x) = 0 :=
  Iff.rfl

/-- The familiar infinitesimal metric-preservation equation is exactly
membership in Mathlib's skew-adjoint endomorphism Lie subalgebra. -/
theorem mem_skewAdjointLieSubalgebra_iff_killing
    (g : V →ₗ[ℝ] V →ₗ[ℝ] ℝ) (D : Module.End ℝ V) :
    D ∈ skewAdjointLieSubalgebra g ↔
      ∀ x y : V, g (D x) y + g x (D y) = 0 := by
  change D ∈ g.skewAdjointSubmodule ↔ _
  rw [LinearMap.mem_skewAdjointSubmodule]
  change (∀ x y : V, g (D x) y = g x (-D y)) ↔ _
  simp only [map_neg, eq_neg_iff_add_eq_zero]

end LinearFunctional

section NoncommutativeAlgebra

variable {A : Type*} [Ring A] [Algebra ℝ A]

/-- Three separate algebraic conditions: a true Leibniz endomorphism,
annihilation by the functional, and skewness for the bilinear form. -/
def IsOperatorialKillingField (ω : A →ₗ[ℝ] ℝ) (g : A →ₗ[ℝ] A →ₗ[ℝ] ℝ)
    (D : Module.End ℝ A) : Prop :=
  InfoGeometry.Algebra.NonAssocDerivation.IsLeibniz ℝ A D ∧
    (∀ a : A, ω (D a) = 0) ∧
      ∀ x y : A, g (D x) y + g x (D y) = 0

/-- The common Lie subalgebra of product, functional, and bilinear-form
infinitesimal symmetries, using the existing noncommutative derivation owner. -/
def operatorialKillingLieSubalgebra
    (ω : A →ₗ[ℝ] ℝ) (g : A →ₗ[ℝ] A →ₗ[ℝ] ℝ) :
    LieSubalgebra ℝ (Module.End ℝ A) :=
  InfoGeometry.Algebra.NonAssocDerivation.derivations ℝ A ⊓
    (functionalAnnihilatingLieSubalgebra ω ⊓ skewAdjointLieSubalgebra g)

@[simp] theorem mem_operatorialKillingLieSubalgebra
    (ω : A →ₗ[ℝ] ℝ) (g : A →ₗ[ℝ] A →ₗ[ℝ] ℝ) (D : Module.End ℝ A) :
    D ∈ operatorialKillingLieSubalgebra ω g ↔ IsOperatorialKillingField ω g D := by
  change (InfoGeometry.Algebra.NonAssocDerivation.IsLeibniz ℝ A D ∧
    (∀ a : A, ω (D a) = 0) ∧ D ∈ skewAdjointLieSubalgebra g) ↔ _
  simp only [IsOperatorialKillingField, mem_skewAdjointLieSubalgebra_iff_killing]

/-- The Killing algebra embeds in the existing actual derivation algebra. -/
theorem operatorialKillingLieSubalgebra_le_derivations
    (ω : A →ₗ[ℝ] ℝ) (g : A →ₗ[ℝ] A →ₗ[ℝ] ℝ) :
    operatorialKillingLieSubalgebra ω g ≤
      InfoGeometry.Algebra.NonAssocDerivation.derivations ℝ A :=
  inf_le_left

/-- The ambient commutator, with its actual composition order, preserves
all three infinitesimal symmetry equations. -/
theorem operatorialKilling_lie
    (ω : A →ₗ[ℝ] ℝ) (g : A →ₗ[ℝ] A →ₗ[ℝ] ℝ)
    {D E : Module.End ℝ A}
    (hD : IsOperatorialKillingField ω g D) (hE : IsOperatorialKillingField ω g E) :
    IsOperatorialKillingField ω g ⁅D, E⁆ := by
  apply (mem_operatorialKillingLieSubalgebra ω g ⁅D, E⁆).mp
  exact (operatorialKillingLieSubalgebra ω g).lie_mem
    ((mem_operatorialKillingLieSubalgebra ω g D).mpr hD)
    ((mem_operatorialKillingLieSubalgebra ω g E).mpr hE)

/-- Every generator satisfying the three symmetry equations gives a native
generated Lie algebra contained in the common Killing algebra. -/
theorem lieSpan_le_operatorialKilling
    (ω : A →ₗ[ℝ] ℝ) (g : A →ₗ[ℝ] A →ₗ[ℝ] ℝ)
    (S : Set (Module.End ℝ A))
    (hS : ∀ D ∈ S, IsOperatorialKillingField ω g D) :
    LieSubalgebra.lieSpan ℝ (Module.End ℝ A) S ≤
      operatorialKillingLieSubalgebra ω g := by
  apply LieSubalgebra.lieSpan_le.mpr
  intro D hD
  exact (mem_operatorialKillingLieSubalgebra ω g D).mpr (hS D hD)

/-- The Lie-span containment is equivalent to the primitive generator
conditions; it adds no hidden commutativity or integration hypothesis. -/
theorem lieSpan_le_operatorialKilling_iff
    (ω : A →ₗ[ℝ] ℝ) (g : A →ₗ[ℝ] A →ₗ[ℝ] ℝ)
    (S : Set (Module.End ℝ A)) :
    LieSubalgebra.lieSpan ℝ (Module.End ℝ A) S ≤
        operatorialKillingLieSubalgebra ω g ↔
      ∀ D ∈ S, IsOperatorialKillingField ω g D := by
  rw [LieSubalgebra.lieSpan_le]
  simp only [Set.subset_def, SetLike.mem_coe, mem_operatorialKillingLieSubalgebra]

end NoncommutativeAlgebra

end InfoGeometry.OperatorAlgebra
