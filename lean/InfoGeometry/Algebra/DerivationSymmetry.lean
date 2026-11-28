/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.Algebra.NonAssocDerivation
import Mathlib.Algebra.Algebra.Equiv
import Mathlib.Algebra.Group.Subgroup.Basic

/-!
# Algebra automorphisms acting on derivations

An algebra automorphism acts on the existing Lie algebra of Leibniz
endomorphisms by conjugation. The algebra itself may be noncommutative.
Derivations annihilated by a linear functional form a Lie subalgebra, and
automorphisms preserving that functional preserve this Lie subalgebra.

For a subgroup of algebra automorphisms, the Lie span of all conjugates of
a generator family is invariant under the subgroup. The conjugation saturation
is part of the construction: no integration or flow invariance of an arbitrary
algebraic Lie span is assumed.
-/

namespace InfoGeometry.Algebra.DerivationSymmetry

open NonAssocDerivation

attribute [local instance 100] LieRing.ofAssociativeRing

variable {R A : Type*} [CommRing R] [Ring A] [Algebra R A]

section Conjugation

/-- Native endomorphism conjugation has the usual pointwise formula. -/
@[simp]
theorem lieConj_apply (α : A ≃ₐ[R] A) (D : Module.End R A) (x : A) :
    α.toLinearEquiv.lieConj D x = α (D (α.symm x)) :=
  rfl

/-- Multiplication preservation transports the Leibniz rule without commuting
any pair of algebra elements or operators. -/
theorem isLeibniz_lieConj (α : A ≃ₐ[R] A) {D : Module.End R A}
    (hD : IsLeibniz R A D) :
    IsLeibniz R A (α.toLinearEquiv.lieConj D) := by
  intro x y
  change α (D (α.symm (x * y))) =
    α (D (α.symm x)) * y + x * α (D (α.symm y))
  rw [_root_.map_mul α.symm, hD, _root_.map_add α, _root_.map_mul α, _root_.map_mul α,
    α.apply_symm_apply, α.apply_symm_apply]

@[simp]
theorem lieConj_one (D : Module.End R A) :
    (1 : A ≃ₐ[R] A).toLinearEquiv.lieConj D = D := by
  ext x
  rfl

/-- The multiplication convention is left composition, as for native `AlgEquiv`. -/
theorem lieConj_mul (α β : A ≃ₐ[R] A) (D : Module.End R A) :
    (α * β).toLinearEquiv.lieConj D =
      α.toLinearEquiv.lieConj (β.toLinearEquiv.lieConj D) := by
  ext x
  rfl

@[simp]
theorem lieConj_symm_lieConj (α : A ≃ₐ[R] A) (D : Module.End R A) :
    α.symm.toLinearEquiv.lieConj (α.toLinearEquiv.lieConj D) = D := by
  ext x
  simp only [lieConj_apply, AlgEquiv.symm_symm, AlgEquiv.symm_apply_apply]

@[simp]
theorem lieConj_lieConj_symm (α : A ≃ₐ[R] A) (D : Module.End R A) :
    α.toLinearEquiv.lieConj (α.symm.toLinearEquiv.lieConj D) = D := by
  ext x
  simp only [lieConj_apply, AlgEquiv.symm_symm, AlgEquiv.apply_symm_apply]

/-- The existing derivation Lie subalgebra is carried onto itself. -/
theorem map_derivations_lieConj (α : A ≃ₐ[R] A) :
    (derivations R A).map
      (α.toLinearEquiv.lieConj : Module.End R A →ₗ⁅R⁆ Module.End R A) =
        derivations R A := by
  ext D
  rw [LieSubalgebra.mem_map]
  constructor
  · rintro ⟨E, hE, rfl⟩
    exact isLeibniz_lieConj α hE
  · intro hD
    exact ⟨α.symm.toLinearEquiv.lieConj D, isLeibniz_lieConj α.symm hD,
      lieConj_lieConj_symm α D⟩

/-- Algebra automorphisms restrict native endomorphism conjugation to a Lie
equivalence of the already bundled derivations. -/
def conjugateDerivation (α : A ≃ₐ[R] A) :
    derivations R A ≃ₗ⁅R⁆ derivations R A :=
  α.toLinearEquiv.lieConj.ofSubalgebras (derivations R A) (derivations R A)
    (map_derivations_lieConj α)

@[simp]
theorem coe_conjugateDerivation (α : A ≃ₐ[R] A) (D : derivations R A) :
    (conjugateDerivation α D : Module.End R A) =
      α.toLinearEquiv.lieConj (D : Module.End R A) :=
  rfl

@[simp]
theorem conjugateDerivation_apply (α : A ≃ₐ[R] A) (D : derivations R A) (x : A) :
    (conjugateDerivation α D : Module.End R A) x =
      α ((D : Module.End R A) (α.symm x)) :=
  rfl

@[simp]
theorem conjugateDerivation_one (D : derivations R A) :
    conjugateDerivation (1 : A ≃ₐ[R] A) D = D := by
  apply Subtype.ext
  exact lieConj_one (D : Module.End R A)

theorem conjugateDerivation_mul (α β : A ≃ₐ[R] A) (D : derivations R A) :
    conjugateDerivation (α * β) D =
      conjugateDerivation α (conjugateDerivation β D) := by
  apply Subtype.ext
  exact lieConj_mul α β (D : Module.End R A)

@[simp]
theorem conjugateDerivation_symm_conjugateDerivation
    (α : A ≃ₐ[R] A) (D : derivations R A) :
    conjugateDerivation α.symm (conjugateDerivation α D) = D := by
  apply Subtype.ext
  exact lieConj_symm_lieConj α (D : Module.End R A)

@[simp]
theorem conjugateDerivation_conjugateDerivation_symm
    (α : A ≃ₐ[R] A) (D : derivations R A) :
    conjugateDerivation α (conjugateDerivation α.symm D) = D := by
  apply Subtype.ext
  exact lieConj_lieConj_symm α (D : Module.End R A)

/-- The conjugation laws supply an actual native group action. This is explicit
data, so consumers can choose it locally without introducing a global action. -/
@[instance_reducible]
def conjugationAction : MulAction (A ≃ₐ[R] A) (derivations R A) where
  smul α D := conjugateDerivation α D
  one_smul := conjugateDerivation_one
  mul_smul := conjugateDerivation_mul

end Conjugation

section Functional

/-- The derivations satisfying `ω ∘ D = 0`, with their inherited commutator. -/
def annihilatingDerivations (ω : A →ₗ[R] R) :
    LieSubalgebra R (derivations R A) where
  carrier := {D | ∀ x : A, ω ((D : Module.End R A) x) = 0}
  zero_mem' := by
    intro x
    change ω (0 : A) = 0
    exact map_zero ω
  add_mem' {D E} hD hE := by
    intro x
    change ω ((D : Module.End R A) x + (E : Module.End R A) x) = 0
    rw [map_add, hD x, hE x, add_zero]
  smul_mem' r D hD := by
    intro x
    change ω (r • (D : Module.End R A) x) = 0
    rw [map_smul, hD x, smul_zero]
  lie_mem' {D E} hD hE := by
    intro x
    change ω ((D : Module.End R A) ((E : Module.End R A) x) -
      (E : Module.End R A) ((D : Module.End R A) x)) = 0
    rw [map_sub, hD, hE, sub_self]

@[simp]
theorem mem_annihilatingDerivations (ω : A →ₗ[R] R) (D : derivations R A) :
    D ∈ annihilatingDerivations ω ↔ ∀ x : A, ω ((D : Module.End R A) x) = 0 :=
  Iff.rfl

/-- Invariance under an equivalence also gives invariance under its inverse. -/
theorem functional_invariant_symm (ω : A →ₗ[R] R) (α : A ≃ₐ[R] A)
    (hω : ∀ x : A, ω (α x) = ω x) :
    ∀ x : A, ω (α.symm x) = ω x := by
  intro x
  simpa only [AlgEquiv.apply_symm_apply] using (hω (α.symm x)).symm

/-- A functional-preserving automorphism sends functional-annihilating
derivations to functional-annihilating derivations. -/
theorem conjugateDerivation_mem_annihilatingDerivations
    (ω : A →ₗ[R] R) (α : A ≃ₐ[R] A)
    (hω : ∀ x : A, ω (α x) = ω x) {D : derivations R A}
    (hD : D ∈ annihilatingDerivations ω) :
    conjugateDerivation α D ∈ annihilatingDerivations ω := by
  intro x
  change ω (α ((D : Module.End R A) (α.symm x))) = 0
  rw [hω]
  exact hD (α.symm x)

theorem map_annihilatingDerivations (ω : A →ₗ[R] R) (α : A ≃ₐ[R] A)
    (hω : ∀ x : A, ω (α x) = ω x) :
    (annihilatingDerivations ω).map
      (conjugateDerivation α : derivations R A →ₗ⁅R⁆ derivations R A) =
        annihilatingDerivations ω := by
  ext D
  rw [LieSubalgebra.mem_map]
  constructor
  · rintro ⟨E, hE, rfl⟩
    exact conjugateDerivation_mem_annihilatingDerivations ω α hω hE
  · intro hD
    refine ⟨conjugateDerivation α.symm D, ?_,
      conjugateDerivation_conjugateDerivation_symm α D⟩
    exact conjugateDerivation_mem_annihilatingDerivations ω α.symm
      (functional_invariant_symm ω α hω) hD

/-- Restriction to the functional-annihilating derivation Lie subalgebra. -/
def annihilatorConjugation (ω : A →ₗ[R] R) (α : A ≃ₐ[R] A)
    (hω : ∀ x : A, ω (α x) = ω x) :
    annihilatingDerivations ω ≃ₗ⁅R⁆ annihilatingDerivations ω :=
  (conjugateDerivation α).ofSubalgebras
    (annihilatingDerivations ω) (annihilatingDerivations ω)
    (map_annihilatingDerivations ω α hω)

end Functional

section GeneratedLieAlgebra

variable (H : Subgroup (A ≃ₐ[R] A)) (S : Set (derivations R A))

/-- Saturate a family of derivations by the specified automorphism subgroup. -/
def conjugates : Set (derivations R A) :=
  {D | ∃ α : H, ∃ E ∈ S, conjugateDerivation (α : A ≃ₐ[R] A) E = D}

theorem subset_conjugates : S ⊆ conjugates H S := by
  intro D hD
  exact ⟨1, D, hD, conjugateDerivation_one D⟩

theorem conjugate_mem_conjugates (α : H) {D : derivations R A}
    (hD : D ∈ conjugates H S) :
    conjugateDerivation (α : A ≃ₐ[R] A) D ∈ conjugates H S := by
  rcases hD with ⟨β, E, hE, rfl⟩
  exact ⟨α * β, E, hE,
    conjugateDerivation_mul (α : A ≃ₐ[R] A) (β : A ≃ₐ[R] A) E⟩

/-- Saturation is invariant as a set, not merely closed in one direction. -/
theorem image_conjugates (α : H) :
    (conjugateDerivation (α : A ≃ₐ[R] A)) '' conjugates H S = conjugates H S := by
  ext D
  constructor
  · rintro ⟨E, hE, rfl⟩
    exact conjugate_mem_conjugates H S α hE
  · intro hD
    refine ⟨conjugateDerivation ((α⁻¹ : H) : A ≃ₐ[R] A) D,
      conjugate_mem_conjugates H S α⁻¹ hD, ?_⟩
    exact conjugateDerivation_conjugateDerivation_symm (α : A ≃ₐ[R] A) D

/-- The Lie algebra generated after conjugation saturation. -/
def conjugationLieSpan : LieSubalgebra R (derivations R A) :=
  LieSubalgebra.lieSpan R (derivations R A) (conjugates H S)

theorem subset_conjugationLieSpan : S ⊆ conjugationLieSpan H S := by
  intro D hD
  exact LieSubalgebra.subset_lieSpan (subset_conjugates H S hD)

/-- Native Lie span commutes with images, hence saturation gives invariance of
the whole generated Lie algebra. -/
theorem map_conjugationLieSpan (α : H) :
    (conjugationLieSpan H S).map
      (conjugateDerivation (α : A ≃ₐ[R] A) :
        derivations R A →ₗ⁅R⁆ derivations R A) = conjugationLieSpan H S := by
  unfold conjugationLieSpan
  rw [LieSubalgebra.map_lieSpan]
  congr 1
  exact image_conjugates H S α

/-- The subgroup acts by actual Lie equivalences on the saturated Lie span. -/
def conjugationLieSpanEquiv (α : H) :
    conjugationLieSpan H S ≃ₗ⁅R⁆ conjugationLieSpan H S :=
  (conjugateDerivation (α : A ≃ₐ[R] A)).ofSubalgebras
    (conjugationLieSpan H S) (conjugationLieSpan H S)
    (map_conjugationLieSpan H S α)

/-- If every generator annihilates the functional and the subgroup preserves
it, the entire conjugation-generated Lie algebra annihilates it. -/
theorem conjugationLieSpan_le_annihilatingDerivations (ω : A →ₗ[R] R)
    (hH : ∀ α : H, ∀ x : A, ω ((α : A ≃ₐ[R] A) x) = ω x)
    (hS : S ⊆ annihilatingDerivations ω) :
    conjugationLieSpan H S ≤ annihilatingDerivations ω := by
  apply LieSubalgebra.lieSpan_le.mpr
  rintro D ⟨α, E, hE, rfl⟩
  exact conjugateDerivation_mem_annihilatingDerivations ω
    (α : A ≃ₐ[R] A) (hH α) (hS hE)

end GeneratedLieAlgebra

end InfoGeometry.Algebra.DerivationSymmetry
