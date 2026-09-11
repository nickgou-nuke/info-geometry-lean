import Mathlib.GroupTheory.PresentedGroup
import InfoGeometry.Algebra.FiniteSpinAlgebra
import Mathlib.RepresentationTheory.Basic
import InfoGeometry.Categorical.FibonacciFusionTreeBraiding

/-!
# Universal property of the two-generator Artin presentation

This owner packages the finite `B₃` presentation without identifying a target
with a particular matrix carrier. A concrete Fibonacci representation is
obtained by supplying its already-proved Artin relation to `braidGroup3Hom`.
No localization, topology, or braided-category instance is asserted here.
-/

namespace InfoGeometry.Categorical.FibonacciBraidGroup3

open InfoGeometry.Categorical.FibonacciFusionTreeBraiding
open InfoGeometry.Categorical.FibonacciFusionTreeLinearEquiv

noncomputable section

abbrev Generator := Fin 2

def braidRelation : FreeGroup Generator :=
  (FreeGroup.of 0 * FreeGroup.of 1 * FreeGroup.of 0) *
    (FreeGroup.of 1 * FreeGroup.of 0 * FreeGroup.of 1)⁻¹

def braidRelations : Set (FreeGroup Generator) := {braidRelation}

abbrev BraidGroup3 := PresentedGroup braidRelations

theorem braidGroup3Hom_of
    {G : Type*} [Group G]
    (f : Generator → G)
    (hArtin : FreeGroup.lift f braidRelation = 1) :
    PresentedGroup.toGroup (fun r hr => by
      have hr' : r = braidRelation := by
        simpa [braidRelations] using hr
      rw [hr']
      exact hArtin) (PresentedGroup.of (0 : Generator)) = f 0 := by
  exact PresentedGroup.toGroup.of _

theorem braidGroup3Hom_of_one
    {G : Type*} [Group G]
    (f : Generator → G)
    (hArtin : FreeGroup.lift f braidRelation = 1) :
    PresentedGroup.toGroup (fun r hr => by
      have hr' : r = braidRelation := by
        simpa [braidRelations] using hr
      rw [hr']
      exact hArtin) (PresentedGroup.of (1 : Generator)) = f 1 := by
  exact PresentedGroup.toGroup.of _

noncomputable def braidGroup3Hom
    {G : Type*} [Group G]
    (f : Generator → G)
    (hArtin : FreeGroup.lift f braidRelation = 1) :
    BraidGroup3 →* G :=
  PresentedGroup.toGroup (fun r hr => by
    have hr' : r = braidRelation := by
      simpa [braidRelations] using hr
    rw [hr']
    exact hArtin)

abbrev FusionAutomorphism := FusionTree ≃ₗ[ℂ] FusionTree

def fibonacciGenerators (q : Units ℂ) (τ s : ℂ)
    (hs : s ^ 2 = τ) (hτ : τ ^ 2 + τ = 1) :
    Generator → FusionAutomorphism := fun i =>
  if i = 0 then rLinearEquiv q else bLinearEquiv q τ s hs hτ

theorem fibonacciGenerators_artin_lift (q : Units ℂ) (τ s : ℂ)
    (hq_inv : (q ^ (-4 : ℤ) : ℂ) = - (q : ℂ))
    (hq_pow3 : (q ^ (3 : ℤ) : ℂ) = (q : ℂ) ^ 3)
    (hq5 : (q : ℂ) ^ 5 = -1)
    (h_poly : (q : ℂ) ^ 4 - (q : ℂ) ^ 3 + (q : ℂ) ^ 2 -
      (q : ℂ) + 1 = 0)
    (hτspec : τ = (q : ℂ) ^ 2 - (q : ℂ) ^ 3)
    (hs : s ^ 2 = τ) (hτ : τ ^ 2 + τ = 1) :
    FreeGroup.lift (fibonacciGenerators q τ s hs hτ) braidRelation = 1 := by
  let R : FusionAutomorphism := rLinearEquiv q
  let B : FusionAutomorphism := bLinearEquiv q τ s hs hτ
  have hArtin : R * B * R = B * R * B := by
    change (R.trans B).trans R = (B.trans R).trans B
    exact fusionTree_artin_equiv q τ s hq_inv hq_pow3 hq5 h_poly hτspec hs hτ
  have hArtinExpanded :
      rLinearEquiv q * bLinearEquiv q τ s hs hτ * rLinearEquiv q =
        bLinearEquiv q τ s hs hτ * rLinearEquiv q *
          bLinearEquiv q τ s hs hτ := by
    simpa [R, B] using hArtin
  simp [braidRelation, FreeGroup.lift_apply_of, fibonacciGenerators, R, B]
  rw [hArtinExpanded]
  group

noncomputable def fibonacciBraidGroup3Hom (q : Units ℂ) (τ s : ℂ)
    (hq_inv : (q ^ (-4 : ℤ) : ℂ) = - (q : ℂ))
    (hq_pow3 : (q ^ (3 : ℤ) : ℂ) = (q : ℂ) ^ 3)
    (hq5 : (q : ℂ) ^ 5 = -1)
    (h_poly : (q : ℂ) ^ 4 - (q : ℂ) ^ 3 + (q : ℂ) ^ 2 -
      (q : ℂ) + 1 = 0)
    (hτspec : τ = (q : ℂ) ^ 2 - (q : ℂ) ^ 3)
    (hs : s ^ 2 = τ) (hτ : τ ^ 2 + τ = 1) :
    BraidGroup3 →* FusionAutomorphism :=
  braidGroup3Hom (fibonacciGenerators q τ s hs hτ)
    (fibonacciGenerators_artin_lift q τ s hq_inv hq_pow3 hq5 h_poly hτspec hs hτ)

end
end InfoGeometry.Categorical.FibonacciBraidGroup3
