/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.Lie.CartanTrialityRepresentation
import InfoGeometry.Geometry.CotangentActionGroupoid
import InfoGeometry.Geometry.FiniteCotangentInvariants
import Mathlib.Algebra.Group.Equiv.TypeTags
import Mathlib.LinearAlgebra.Basis.VectorSpace
import Mathlib.LinearAlgebra.Dual.Lemmas

/-!
# Cartan S₃ on the algebraic cotangent groupoid of the real vector group

The four-dimensional representation acts by genuine automorphisms of the
additive group of its vector space. That vector group has trivial adjoint
representation, so the general contragredient lift gives native groupoid
equivalences. The actual fixed primal/dual pairs form a four-dimensional
space with a nondegenerate alternating form, canonically the cotangent space
of the two-dimensional fixed Cartan plane.

All groupoid and form constructions here are algebraic. No identification
with the cotangent groupoid of Spin(4,4), or with a smooth G₂ fixed manifold,
is inferred from the Cartan matrices.
-/

set_option autoImplicit false
noncomputable section

namespace InfoGeometry.Lie.CartanTrialityCotangent

open CategoryTheory
open InfoGeometry.Lie.CartanTriality
open InfoGeometry.Geometry.CotangentActionGroupoid
open InfoGeometry.Geometry.FiniteCotangentInvariants
open InfoGeometry.Canonical.SouriauContragredientPairing
open InfoGeometry.Clifford.NeutralPhaseSpaceCore

/-- The four-dimensional action as Mathlib's native real representation. -/
def cartanRepresentation : Representation ℝ (Equiv.Perm (Fin 3)) (Fin 4 → ℝ) :=
  LinearEquiv.automorphismGroup.toLinearMapMonoidHom.comp s3LinearAction

@[simp] theorem cartanRepresentation_apply (s : Equiv.Perm (Fin 3)) (v : Fin 4 → ℝ) :
    cartanRepresentation s v = s3LinearAction s v := rfl

/-- The native representation invariants coincide with the exact generator-fixed plane. -/
theorem cartanRepresentation_invariants : cartanRepresentation.invariants = fixedCartan := by
  ext v
  change (∀ s : Equiv.Perm (Fin 3), s3LinearAction s v = v) ↔ v ∈ fixedCartan
  exact fixed_by_s3_iff v

/-- This dual action is precisely the contragredient used by the groupoid lift. -/
theorem contragredient_eq_dual (s : Equiv.Perm (Fin 3))
    (α : Module.Dual ℝ (Fin 4 → ℝ)) :
    contragredient (s3LinearAction s) α = cartanRepresentation.dual s α := by
  apply LinearMap.ext
  intro v
  change α ((s3LinearAction s).symm v) = α (s3LinearAction s⁻¹ v)
  rw [map_inv]
  rfl

/-- The additive vector group, written multiplicatively for the groupoid API. -/
abbrev CartanVectorGroup := Multiplicative (Fin 4 → ℝ)

/-- The trivial adjoint model for an abelian vector group. -/
def vectorAdjoint : CartanVectorGroup →* ((Fin 4 → ℝ) ≃ₗ[ℝ] (Fin 4 → ℝ)) where
  toFun _ := LinearEquiv.refl ℝ (Fin 4 → ℝ)
  map_one' := rfl
  map_mul' _ _ := rfl

/-- Each Cartan symmetry is an automorphism of the full additive vector group. -/
def vectorGroupAuto (s : Equiv.Perm (Fin 3)) : CartanVectorGroup ≃* CartanVectorGroup :=
  AddEquiv.toMultiplicative (s3LinearAction s).toAddEquiv

@[simp] theorem vectorGroupAuto_apply (s : Equiv.Perm (Fin 3)) (k : CartanVectorGroup) :
    (vectorGroupAuto s k).toAdd = s3LinearAction s k.toAdd := rfl

/-- Equivariance with the specified trivial adjoint model is automatic. -/
theorem vectorAdjoint_intertwine (s : Equiv.Perm (Fin 3))
    (k : CartanVectorGroup) (v : Fin 4 → ℝ) :
    s3LinearAction s (vectorAdjoint k v) =
      vectorAdjoint (vectorGroupAuto s k) (s3LinearAction s v) := rfl

/-- A native equivalence of the vector-group cotangent action groupoid. -/
def vectorCotangentEquivalence (s : Equiv.Perm (Fin 3)) :
    CotangentGroupoid vectorAdjoint ≌ CotangentGroupoid vectorAdjoint :=
  liftEquivalence vectorAdjoint (vectorGroupAuto s) (s3LinearAction s)
    (vectorAdjoint_intertwine s)

/-- In the vector-group specialization every arrow has equal source and target. -/
theorem vector_target_eq_source (x : Arrow (R := ℝ) CartanVectorGroup (Fin 4 → ℝ)) :
    target vectorAdjoint x = source x := by
  apply LinearMap.ext
  intro v
  rfl

/-- Composable vector-group arrows compose by addition of the group coordinates. -/
theorem vector_comp_coordinate
    (x y : Arrow (R := ℝ) CartanVectorGroup (Fin 4 → ℝ))
    (h : Composable vectorAdjoint x y) :
    (comp vectorAdjoint x y h).1.toAdd = x.1.toAdd + y.1.toAdd := rfl

/-- Fixing all lifted arrows is exactly fixing their primal and dual coordinates. -/
theorem fixed_vector_arrows_iff
    (x : Arrow (R := ℝ) CartanVectorGroup (Fin 4 → ℝ)) :
    (∀ s : Equiv.Perm (Fin 3), lift (vectorGroupAuto s) (s3LinearAction s) x = x) ↔
      x.1.toAdd ∈ cartanRepresentation.invariants ∧ x.2 ∈ cartanRepresentation.dual.invariants := by
  simp only [lift_fixed_iff, contragredient_eq_dual, forall_and]
  rfl

/-- The cotangent linear lift on tangent/primal-dual coordinates. -/
def phaseAction (s : Equiv.Perm (Fin 3)) :
    PhaseSpaceCarrier (Fin 4 → ℝ) ≃ₗ[ℝ] PhaseSpaceCarrier (Fin 4 → ℝ) :=
  InfoGeometry.Geometry.CotangentLieForm.cotangentLift (s3LinearAction s)

/-- The actual ambient alternating form is invariant under every lifted Cartan symmetry. -/
theorem phaseAction_preserves_omega (s : Equiv.Perm (Fin 3))
    (z w : PhaseSpaceCarrier (Fin 4 → ℝ)) :
    neutralOmega (phaseAction s z) (phaseAction s w) = neutralOmega z w := by
  exact InfoGeometry.Geometry.CotangentLieForm.cotangentLift_omega (s3LinearAction s) z w

/-- All-element fixed vectors are the actual invariant primal and invariant dual spaces. -/
theorem fixed_phase_iff (z : PhaseSpaceCarrier (Fin 4 → ℝ)) :
    (∀ s : Equiv.Perm (Fin 3), phaseAction s z = z) ↔
      z.1 ∈ cartanRepresentation.invariants ∧ z.2 ∈ cartanRepresentation.dual.invariants := by
  change (∀ s : Equiv.Perm (Fin 3),
    (s3LinearAction s z.1, contragredient (s3LinearAction s) z.2) = (z.1, z.2)) ↔ _
  simp only [Prod.mk.injEq, contragredient_eq_dual, forall_and]
  rfl

/-- Coordinate equality gives the native equivalence with the proved fixed Cartan plane. -/
def invariantCartanEquiv : cartanRepresentation.invariants ≃ₗ[ℝ] fixedCartan :=
  LinearEquiv.ofEq _ _ cartanRepresentation_invariants

/-- Restriction identifies the actual fixed covectors with the dual of the Cartan plane. -/
def invariantCartanDualEquiv :
    cartanRepresentation.dual.invariants ≃ₗ[ℝ] Module.Dual ℝ fixedCartan :=
  (invariantDualEquiv cartanRepresentation).trans invariantCartanEquiv.symm.dualMap

/-- Fixed phase coordinates are canonically the cotangent space of the fixed plane. -/
def fixedCartanCotangentEquiv :
    (cartanRepresentation.invariants × cartanRepresentation.dual.invariants) ≃ₗ[ℝ]
      PhaseSpaceCarrier fixedCartan :=
  invariantCartanEquiv.prodCongr invariantCartanDualEquiv

/-- The explicit fixed-plane identification preserves the restricted ambient form. -/
theorem fixedCartanCotangentEquiv_omega
    (z w : cartanRepresentation.invariants × cartanRepresentation.dual.invariants) :
    neutralOmega (fixedPhaseInclusion cartanRepresentation z)
        (fixedPhaseInclusion cartanRepresentation w) =
      neutralOmega (fixedCartanCotangentEquiv z) (fixedCartanCotangentEquiv w) := by
  simp [fixedCartanCotangentEquiv, fixedPhaseInclusion, neutralOmega_apply,
    invariantCartanDualEquiv]

theorem finrank_cartan_invariants : Module.finrank ℝ cartanRepresentation.invariants = 2 := by
  rw [cartanRepresentation_invariants]
  exact finrank_fixedCartan

theorem finrank_cartan_dual_invariants : Module.finrank ℝ cartanRepresentation.dual.invariants = 2 := by
  calc
    Module.finrank ℝ cartanRepresentation.dual.invariants =
        Module.finrank ℝ (Module.Dual ℝ fixedCartan) := invariantCartanDualEquiv.finrank_eq
    _ = Module.finrank ℝ fixedCartan := Subspace.dual_finrank_eq
    _ = 2 := finrank_fixedCartan

/-- The simultaneous fixed cotangent space has the expected actual dimension four. -/
theorem finrank_fixed_cartan_phase :
    Module.finrank ℝ (cartanRepresentation.invariants × cartanRepresentation.dual.invariants) = 4 := by
  rw [Module.finrank_prod, finrank_cartan_invariants, finrank_cartan_dual_invariants]

/-- Finite triality gives a nondegenerate form on the actual fixed coordinates. -/
theorem fixed_cartan_phase_nondegenerate :
    (fixedCotangentForm cartanRepresentation).Nondegenerate :=
  fixedCotangentForm_nondegenerate cartanRepresentation

/-- The restricted form is alternating as well as nondegenerate. -/
theorem fixed_cartan_phase_isAlt : (fixedCotangentForm cartanRepresentation).IsAlt :=
  fixedCotangentForm_isAlt cartanRepresentation

end InfoGeometry.Lie.CartanTrialityCotangent
