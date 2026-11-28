/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.OperatorAlgebra.OperatorialKillingLieClosure
import InfoGeometry.OperatorAlgebra.OperatorInvariantErlangenClosure
import InfoGeometry.OperatorAlgebra.OperatorKillingExponential

/-!
# Bounded Killing generators, automorphism flows, and Erlangen closure

This owner connects the infinitesimal and global constructions on the same
real algebra. A bounded continuous endomorphism satisfying the three actual
Killing equations is integrated using the existing operator exponential.
Its derivative is the specified generator, and every time map preserves the
specified continuous functional and bilinear form. A whole family therefore
has its genuine invariant-pair Erlangen closure in their common stabilizer.

The analytic assumptions belong to this bridge, not to the algebraic Lie-span
theorem. No unbounded modular generator or Tomita standard form is introduced.
-/

noncomputable section

namespace InfoGeometry.OperatorAlgebra.OperatorKillingErlangenBridge

open InfoGeometry.Canonical.FlowErlangenClosure
open InfoGeometry.Lie.ContinuousDerivationExponential
open OperatorInvariantErlangenClosure OperatorKillingExponential
open scoped OperatorInvariantPullback

variable {A : Type*} [NormedRing A] [NormedAlgebra ℝ A] [CompleteSpace A]

/-- Differentiating a preserving algebra-automorphism flow recovers all three
infinitesimal Killing equations. The equations are conclusions here. -/
theorem isOperatorialKilling_of_differentiable_invariant_flow
    (ω : A →L[ℝ] ℝ) (B : A →L[ℝ] A →L[ℝ] ℝ)
    (Φ : Multiplicative ℝ →* (A ≃ₐ[ℝ] A)) (D : A →L[ℝ] A)
    (hΦ : ∀ x : A,
      HasDerivAt (fun t : ℝ => Φ (Multiplicative.ofAdd t) x) (D x) 0)
    (hω : ∀ (t : Multiplicative ℝ) (x : A), ω (Φ t x) = ω x)
    (hB : ∀ (t : Multiplicative ℝ) (x y : A), B (Φ t x) (Φ t y) = B x y) :
    IsOperatorialKillingField ω.toLinearMap (continuousBilinForm B) D.toLinearMap := by
  exact ⟨isDerivation_of_hasDerivAt_automorphismFlow Φ D hΦ,
    functional_generator_eq_zero_of_flow_invariant Φ D hΦ ω hω,
    bilinForm_generator_skew_of_flow_invariant Φ D hΦ B hB⟩

/-- The infinitesimal Leibniz equation is exactly the continuous multiplication
equation used by the already proved exponential integration theorem. -/
theorem continuous_leibniz_of_killing
    (ω : A →L[ℝ] ℝ) (B : A →L[ℝ] A →L[ℝ] ℝ) (D : A →L[ℝ] A)
    (hD : IsOperatorialKillingField ω.toLinearMap (continuousBilinForm B) D.toLinearMap) :
    IsDerivation (ContinuousLinearMap.mul ℝ A) D :=
  hD.1

/-- The actual automorphism group integrated from a bounded Killing generator. -/
def boundedKillingFlowHom
    (ω : A →L[ℝ] ℝ) (B : A →L[ℝ] A →L[ℝ] ℝ) (D : A →L[ℝ] A)
    (hD : IsOperatorialKillingField ω.toLinearMap (continuousBilinForm B) D.toLinearMap) :
    Multiplicative ℝ →* (A ≃ₐ[ℝ] A) :=
  flowAlgEquivHom D (continuous_leibniz_of_killing ω B D hD)

/-- The constructed motion differentiates to the original endomorphism. -/
theorem hasDerivAt_boundedKillingFlow_zero
    (ω : A →L[ℝ] ℝ) (B : A →L[ℝ] A →L[ℝ] ℝ) (D : A →L[ℝ] A)
    (hD : IsOperatorialKillingField ω.toLinearMap (continuousBilinForm B) D.toLinearMap)
    (x : A) :
    HasDerivAt
      (fun t : ℝ => boundedKillingFlowHom ω B D hD (Multiplicative.ofAdd t) x)
      (D x) 0 :=
  hasDerivAt_flowAlgEquiv_zero D (continuous_leibniz_of_killing ω B D hD) x

/-- Functional and form preservation follow from the infinitesimal equations
by differentiating the exponential orbits, not from assumed flow invariance. -/
theorem boundedKillingFlow_mem_stabilizer
    (ω : A →L[ℝ] ℝ) (B : A →L[ℝ] A →L[ℝ] ℝ) (D : A →L[ℝ] A)
    (hD : IsOperatorialKillingField ω.toLinearMap (continuousBilinForm B) D.toLinearMap)
    (t : Multiplicative ℝ) :
    boundedKillingFlowHom ω B D hD t ∈
      functionalFormAutomorphismSubgroup ω.toLinearMap (continuousBilinForm B) := by
  rw [mem_functionalFormAutomorphismSubgroup_iff]
  exact flowAlgEquivHom_preserves_invariants D
    (continuous_leibniz_of_killing ω B D hD) ω B hD.2.1 hD.2.2 t

/-- For a bounded continuous generator on a complete real normed algebra,
the Killing conditions are equivalent to the existence of an actual
preserving automorphism flow with that specified derivative at zero. -/
theorem isOperatorialKilling_iff_exists_invariant_flow
    (ω : A →L[ℝ] ℝ) (B : A →L[ℝ] A →L[ℝ] ℝ) (D : A →L[ℝ] A) :
    IsOperatorialKillingField ω.toLinearMap (continuousBilinForm B) D.toLinearMap ↔
      ∃ Φ : Multiplicative ℝ →* (A ≃ₐ[ℝ] A),
        (∀ x : A, HasDerivAt (fun t : ℝ => Φ (Multiplicative.ofAdd t) x) (D x) 0) ∧
        (∀ (t : Multiplicative ℝ) (x : A), ω (Φ t x) = ω x) ∧
        (∀ (t : Multiplicative ℝ) (x y : A), B (Φ t x) (Φ t y) = B x y) := by
  constructor
  · intro hD
    refine ⟨boundedKillingFlowHom ω B D hD,
      hasDerivAt_boundedKillingFlow_zero ω B D hD, ?_, ?_⟩
    · intro t x
      exact ((mem_functionalFormAutomorphismSubgroup_iff _ _ _).mp
        (boundedKillingFlow_mem_stabilizer ω B D hD t)).1 x
    · intro t x y
      exact ((mem_functionalFormAutomorphismSubgroup_iff _ _ _).mp
        (boundedKillingFlow_mem_stabilizer ω B D hD t)).2 x y
  · rintro ⟨Φ, hΦ, hω, hB⟩
    exact isOperatorialKilling_of_differentiable_invariant_flow ω B Φ D hΦ hω hB

/-- A family of bounded Killing generators gives a generated flow subgroup
and a genuine invariant-pair closure inside the common automorphism stabilizer. -/
theorem boundedKillingFamily_erlangen_closure
    {ι : Type*} (ω : A →L[ℝ] ℝ) (B : A →L[ℝ] A →L[ℝ] ℝ)
    (D : ι → A →L[ℝ] A)
    (hD : ∀ i, IsOperatorialKillingField ω.toLinearMap (continuousBilinForm B)
      (D i).toLinearMap) :
    flowFamilySubgroup (fun i => boundedKillingFlowHom ω B (D i) (hD i)) ≤
        symmetryClosure (A ≃ₐ[ℝ] A)
          ((A →ₗ[ℝ] ℝ) × LinearMap.BilinForm ℝ A)
          (flowFamilySubgroup (fun i => boundedKillingFlowHom ω B (D i) (hD i))) ∧
      symmetryClosure (A ≃ₐ[ℝ] A)
          ((A →ₗ[ℝ] ℝ) × LinearMap.BilinForm ℝ A)
          (flowFamilySubgroup (fun i => boundedKillingFlowHom ω B (D i) (hD i))) ≤
        functionalFormAutomorphismSubgroup ω.toLinearMap (continuousBilinForm B) := by
  apply automorphism_flowFamily_erlangen_closure
  · intro i t
    exact (flowAlgEquivHom_preserves_invariants (D i)
      (continuous_leibniz_of_killing ω B (D i) (hD i)) ω B (hD i).2.1 (hD i).2.2 t).1
  · intro i t
    exact (flowAlgEquivHom_preserves_invariants (D i)
      (continuous_leibniz_of_killing ω B (D i) (hD i)) ω B (hD i).2.1 (hD i).2.2 t).2

end InfoGeometry.OperatorAlgebra.OperatorKillingErlangenBridge
