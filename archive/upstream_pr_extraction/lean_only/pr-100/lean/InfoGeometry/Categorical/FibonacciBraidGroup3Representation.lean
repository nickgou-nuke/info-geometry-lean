import Mathlib.GroupTheory.PresentedGroup
import Mathlib.RepresentationTheory.Basic
import InfoGeometry.Categorical.FibonacciFusionTreeBraiding

/-!
# The presented three-strand braid group and its Fibonacci representation

This file defines the abstract braid group `B₃` as a Mathlib `PresentedGroup`
on two generators with the Artin relation

`σ₁ σ₂ σ₁ = σ₂ σ₁ σ₂`.

It then proves the universal representation theorem: any pair of elements of a
group satisfying the Artin relation induces a unique group homomorphism from
`BraidGroup3`.

Finally, the already verified finite Fibonacci operators

* `rLinearEquiv q`, and
* `bLinearEquiv q τ s hs hτ`

are used as the two generator images.  The existing kernel-checked
`fusionTree_artin` theorem supplies the defining relation, yielding both a
group homomorphism into the group of complex linear automorphisms of the
fusion-tree carrier and the corresponding Mathlib `Representation`.

No positive-monoid localization, Garside normal form, configuration-space
fibration, categorical braiding instance, CPT identification, or faithfulness
claim is made here.
-/

set_option autoImplicit false

namespace InfoGeometry.Categorical.FibonacciBraidGroup3Representation

open InfoGeometry.Categorical.FibonacciFusionTreeLinearEquiv
open InfoGeometry.Categorical.FibonacciFusionTreeBraiding

/-! ## The abstract presented braid group `B₃` -/

/-- The two standard Artin generators of the three-strand braid group. -/
inductive BraidGenerator3 where
  | sigmaOne
  | sigmaTwo
  deriving DecidableEq

/-- The first generator in the free group. -/
def freeSigmaOne : FreeGroup BraidGenerator3 :=
  FreeGroup.of BraidGenerator3.sigmaOne

/-- The second generator in the free group. -/
def freeSigmaTwo : FreeGroup BraidGenerator3 :=
  FreeGroup.of BraidGenerator3.sigmaTwo

/-- The relator `σ₁ σ₂ σ₁ (σ₂ σ₁ σ₂)⁻¹`. -/
def braidThreeArtinRelator : FreeGroup BraidGenerator3 :=
  freeSigmaOne * freeSigmaTwo * freeSigmaOne *
    (freeSigmaTwo * freeSigmaOne * freeSigmaTwo)⁻¹

/-- The singleton relation set defining `B₃`. -/
def braidThreeRelations : Set (FreeGroup BraidGenerator3) :=
  {braidThreeArtinRelator}

/-- The three-strand braid group, presented by two generators and the Artin
relation. -/
abbrev BraidGroup3 := PresentedGroup braidThreeRelations

/-- The first canonical generator of `BraidGroup3`. -/
def sigmaOne : BraidGroup3 :=
  PresentedGroup.of BraidGenerator3.sigmaOne

/-- The second canonical generator of `BraidGroup3`. -/
def sigmaTwo : BraidGroup3 :=
  PresentedGroup.of BraidGenerator3.sigmaTwo

/-- The defining Artin relation holds in the presented group. -/
theorem braidGroup3_artin :
    sigmaOne * sigmaTwo * sigmaOne =
      sigmaTwo * sigmaOne * sigmaTwo := by
  apply eq_of_mul_inv_eq_one
  have hrel :
      PresentedGroup.mk braidThreeRelations braidThreeArtinRelator =
        (1 : BraidGroup3) :=
    PresentedGroup.one_of_mem
      (show braidThreeArtinRelator ∈ braidThreeRelations by
        simp [braidThreeRelations])
  simpa [sigmaOne, sigmaTwo, braidThreeArtinRelator,
    freeSigmaOne, freeSigmaTwo] using hrel

/-! ## Universal group-valued Artin data -/

/-- A pair of elements in a group satisfying the three-strand Artin relation. -/
structure BraidThreeGenerators (G : Type*) [Group G] where
  sigmaOne : G
  sigmaTwo : G
  artin :
    sigmaOne * sigmaTwo * sigmaOne =
      sigmaTwo * sigmaOne * sigmaTwo

namespace BraidThreeGenerators

variable {G : Type*} [Group G]

/-- Images of the two abstract generators. -/
def generatorImage (R : BraidThreeGenerators G) :
    BraidGenerator3 → G
  | .sigmaOne => R.sigmaOne
  | .sigmaTwo => R.sigmaTwo

/-- The Artin relator evaluates to the identity under any Artin pair. -/
theorem relation_lift_eq_one (R : BraidThreeGenerators G) :
    ∀ r ∈ braidThreeRelations,
      FreeGroup.lift R.generatorImage r = 1 := by
  intro r hr
  have hr' : r = braidThreeArtinRelator := by
    simpa [braidThreeRelations] using hr
  subst r
  simp [braidThreeArtinRelator, freeSigmaOne, freeSigmaTwo,
    generatorImage, mul_assoc]
  simp only [← mul_assoc]
  rw [R.artin]
  simp

/-- Universal group homomorphism from the presented braid group. -/
def toGroupHom (R : BraidThreeGenerators G) :
    BraidGroup3 →* G :=
  PresentedGroup.toGroup
    (f := R.generatorImage)
    R.relation_lift_eq_one

@[simp]
theorem toGroupHom_sigmaOne (R : BraidThreeGenerators G) :
    R.toGroupHom
        InfoGeometry.Categorical.FibonacciBraidGroup3Representation.sigmaOne =
      R.sigmaOne := by
  exact PresentedGroup.toGroup.of R.relation_lift_eq_one

@[simp]
theorem toGroupHom_sigmaTwo (R : BraidThreeGenerators G) :
    R.toGroupHom
        InfoGeometry.Categorical.FibonacciBraidGroup3Representation.sigmaTwo =
      R.sigmaTwo := by
  exact PresentedGroup.toGroup.of R.relation_lift_eq_one

@[simp]
theorem toGroupHom_sigmaOne_inv (R : BraidThreeGenerators G) :
    R.toGroupHom
        InfoGeometry.Categorical.FibonacciBraidGroup3Representation.sigmaOne⁻¹ =
      R.sigmaOne⁻¹ := by
  simpa using map_inv R.toGroupHom
    InfoGeometry.Categorical.FibonacciBraidGroup3Representation.sigmaOne

@[simp]
theorem toGroupHom_sigmaTwo_inv (R : BraidThreeGenerators G) :
    R.toGroupHom
        InfoGeometry.Categorical.FibonacciBraidGroup3Representation.sigmaTwo⁻¹ =
      R.sigmaTwo⁻¹ := by
  simpa using map_inv R.toGroupHom
    InfoGeometry.Categorical.FibonacciBraidGroup3Representation.sigmaTwo

/-- Inverse generators satisfy the inverse Artin relation. -/
theorem inverse_artin (R : BraidThreeGenerators G) :
    R.sigmaOne⁻¹ * R.sigmaTwo⁻¹ * R.sigmaOne⁻¹ =
      R.sigmaTwo⁻¹ * R.sigmaOne⁻¹ * R.sigmaTwo⁻¹ := by
  have h := congrArg (fun g : G => g⁻¹) R.artin
  simpa [mul_assoc] using h

/-- A homomorphism out of `BraidGroup3` is determined by the two generator
images. -/
theorem toGroupHom_unique
    (R : BraidThreeGenerators G)
    (φ : BraidGroup3 →* G)
    (h₁ : φ InfoGeometry.Categorical.FibonacciBraidGroup3Representation.sigmaOne =
      R.sigmaOne)
    (h₂ : φ InfoGeometry.Categorical.FibonacciBraidGroup3Representation.sigmaTwo =
      R.sigmaTwo) :
    φ = R.toGroupHom := by
  apply PresentedGroup.ext
  intro g
  cases g
  · exact h₁.trans (toGroupHom_sigmaOne R).symm
  · exact h₂.trans (toGroupHom_sigmaTwo R).symm

end BraidThreeGenerators

/-! ## Fibonacci specialization -/

/-- The verified Fibonacci `R` and `B = F R F` linear equivalences form an
Artin pair. -/
noncomputable def fibonacciGenerators
    (q : Units ℂ) (τ s : ℂ)
    (hq_inv : (q ^ (-4 : ℤ) : ℂ) = - (q : ℂ))
    (hq_pow3 : (q ^ (3 : ℤ) : ℂ) = (q : ℂ) ^ 3)
    (hq5 : (q : ℂ) ^ 5 = -1)
    (h_poly : (q : ℂ) ^ 4 - (q : ℂ) ^ 3 + (q : ℂ) ^ 2 -
      (q : ℂ) + 1 = 0)
    (hτq : τ = (q : ℂ) ^ 2 - (q : ℂ) ^ 3)
    (hs : s ^ 2 = τ)
    (hτ : τ ^ 2 + τ = 1) :
    BraidThreeGenerators (FusionTree ≃ₗ[ℂ] FusionTree) where
  sigmaOne := rLinearEquiv q
  sigmaTwo := bLinearEquiv q τ s hs hτ
  artin := by
    apply LinearEquiv.ext
    intro x
    change
      rLinearMap q (bLinearMap q τ s (rLinearMap q x)) =
        bLinearMap q τ s (rLinearMap q (bLinearMap q τ s x))
    exact congrArg
      (fun f : FusionTree →ₗ[ℂ] FusionTree => f x)
      (fusionTree_artin q τ s hq_inv hq_pow3 hq5 h_poly hτq hs)

/-- The group-level Fibonacci action of the presented braid group. -/
noncomputable def fibonacciBraidGroupHom
    (q : Units ℂ) (τ s : ℂ)
    (hq_inv : (q ^ (-4 : ℤ) : ℂ) = - (q : ℂ))
    (hq_pow3 : (q ^ (3 : ℤ) : ℂ) = (q : ℂ) ^ 3)
    (hq5 : (q : ℂ) ^ 5 = -1)
    (h_poly : (q : ℂ) ^ 4 - (q : ℂ) ^ 3 + (q : ℂ) ^ 2 -
      (q : ℂ) + 1 = 0)
    (hτq : τ = (q : ℂ) ^ 2 - (q : ℂ) ^ 3)
    (hs : s ^ 2 = τ)
    (hτ : τ ^ 2 + τ = 1) :
    BraidGroup3 →* (FusionTree ≃ₗ[ℂ] FusionTree) :=
  (fibonacciGenerators q τ s hq_inv hq_pow3 hq5 h_poly hτq hs hτ).toGroupHom

/-- The corresponding Mathlib representation on the fusion-tree module. -/
noncomputable def fibonacciBraidRepresentation
    (q : Units ℂ) (τ s : ℂ)
    (hq_inv : (q ^ (-4 : ℤ) : ℂ) = - (q : ℂ))
    (hq_pow3 : (q ^ (3 : ℤ) : ℂ) = (q : ℂ) ^ 3)
    (hq5 : (q : ℂ) ^ 5 = -1)
    (h_poly : (q : ℂ) ^ 4 - (q : ℂ) ^ 3 + (q : ℂ) ^ 2 -
      (q : ℂ) + 1 = 0)
    (hτq : τ = (q : ℂ) ^ 2 - (q : ℂ) ^ 3)
    (hs : s ^ 2 = τ)
    (hτ : τ ^ 2 + τ = 1) :
    Representation ℂ BraidGroup3 FusionTree :=
  LinearEquiv.automorphismGroup.toLinearMapMonoidHom.comp
    (fibonacciBraidGroupHom q τ s hq_inv hq_pow3 hq5 h_poly hτq hs hτ)

@[simp]
theorem fibonacciBraidGroupHom_sigmaOne
    (q : Units ℂ) (τ s : ℂ)
    (hq_inv : (q ^ (-4 : ℤ) : ℂ) = - (q : ℂ))
    (hq_pow3 : (q ^ (3 : ℤ) : ℂ) = (q : ℂ) ^ 3)
    (hq5 : (q : ℂ) ^ 5 = -1)
    (h_poly : (q : ℂ) ^ 4 - (q : ℂ) ^ 3 + (q : ℂ) ^ 2 -
      (q : ℂ) + 1 = 0)
    (hτq : τ = (q : ℂ) ^ 2 - (q : ℂ) ^ 3)
    (hs : s ^ 2 = τ)
    (hτ : τ ^ 2 + τ = 1) :
    fibonacciBraidGroupHom q τ s hq_inv hq_pow3 hq5 h_poly hτq hs hτ
        InfoGeometry.Categorical.FibonacciBraidGroup3Representation.sigmaOne =
      rLinearEquiv q := by
  simp [fibonacciBraidGroupHom, fibonacciGenerators]

@[simp]
theorem fibonacciBraidGroupHom_sigmaTwo
    (q : Units ℂ) (τ s : ℂ)
    (hq_inv : (q ^ (-4 : ℤ) : ℂ) = - (q : ℂ))
    (hq_pow3 : (q ^ (3 : ℤ) : ℂ) = (q : ℂ) ^ 3)
    (hq5 : (q : ℂ) ^ 5 = -1)
    (h_poly : (q : ℂ) ^ 4 - (q : ℂ) ^ 3 + (q : ℂ) ^ 2 -
      (q : ℂ) + 1 = 0)
    (hτq : τ = (q : ℂ) ^ 2 - (q : ℂ) ^ 3)
    (hs : s ^ 2 = τ)
    (hτ : τ ^ 2 + τ = 1) :
    fibonacciBraidGroupHom q τ s hq_inv hq_pow3 hq5 h_poly hτq hs hτ
        InfoGeometry.Categorical.FibonacciBraidGroup3Representation.sigmaTwo =
      bLinearEquiv q τ s hs hτ := by
  simp [fibonacciBraidGroupHom, fibonacciGenerators]

@[simp]
theorem fibonacciBraidGroupHom_sigmaOne_inv
    (q : Units ℂ) (τ s : ℂ)
    (hq_inv : (q ^ (-4 : ℤ) : ℂ) = - (q : ℂ))
    (hq_pow3 : (q ^ (3 : ℤ) : ℂ) = (q : ℂ) ^ 3)
    (hq5 : (q : ℂ) ^ 5 = -1)
    (h_poly : (q : ℂ) ^ 4 - (q : ℂ) ^ 3 + (q : ℂ) ^ 2 -
      (q : ℂ) + 1 = 0)
    (hτq : τ = (q : ℂ) ^ 2 - (q : ℂ) ^ 3)
    (hs : s ^ 2 = τ)
    (hτ : τ ^ 2 + τ = 1) :
    fibonacciBraidGroupHom q τ s hq_inv hq_pow3 hq5 h_poly hτq hs hτ
        InfoGeometry.Categorical.FibonacciBraidGroup3Representation.sigmaOne⁻¹ =
      rLinearEquiv q⁻¹ := by
  change (rLinearEquiv q).symm = rLinearEquiv q⁻¹
  exact rLinearEquiv_inverse q

@[simp]
theorem fibonacciBraidGroupHom_sigmaTwo_inv
    (q : Units ℂ) (τ s : ℂ)
    (hq_inv : (q ^ (-4 : ℤ) : ℂ) = - (q : ℂ))
    (hq_pow3 : (q ^ (3 : ℤ) : ℂ) = (q : ℂ) ^ 3)
    (hq5 : (q : ℂ) ^ 5 = -1)
    (h_poly : (q : ℂ) ^ 4 - (q : ℂ) ^ 3 + (q : ℂ) ^ 2 -
      (q : ℂ) + 1 = 0)
    (hτq : τ = (q : ℂ) ^ 2 - (q : ℂ) ^ 3)
    (hs : s ^ 2 = τ)
    (hτ : τ ^ 2 + τ = 1) :
    fibonacciBraidGroupHom q τ s hq_inv hq_pow3 hq5 h_poly hτq hs hτ
        InfoGeometry.Categorical.FibonacciBraidGroup3Representation.sigmaTwo⁻¹ =
      bLinearEquiv q⁻¹ τ s hs hτ := by
  change (bLinearEquiv q τ s hs hτ).symm = bLinearEquiv q⁻¹ τ s hs hτ
  exact bLinearEquiv_inverse q τ s hs hτ

@[simp]
theorem fibonacciBraidRepresentation_sigmaOne
    (q : Units ℂ) (τ s : ℂ)
    (hq_inv : (q ^ (-4 : ℤ) : ℂ) = - (q : ℂ))
    (hq_pow3 : (q ^ (3 : ℤ) : ℂ) = (q : ℂ) ^ 3)
    (hq5 : (q : ℂ) ^ 5 = -1)
    (h_poly : (q : ℂ) ^ 4 - (q : ℂ) ^ 3 + (q : ℂ) ^ 2 -
      (q : ℂ) + 1 = 0)
    (hτq : τ = (q : ℂ) ^ 2 - (q : ℂ) ^ 3)
    (hs : s ^ 2 = τ)
    (hτ : τ ^ 2 + τ = 1) :
    fibonacciBraidRepresentation q τ s hq_inv hq_pow3 hq5 h_poly hτq hs hτ sigmaOne =
      rLinearMap q := by
  change
    (fibonacciBraidGroupHom q τ s hq_inv hq_pow3 hq5 h_poly hτq hs hτ sigmaOne).toLinearMap =
      rLinearMap q
  rw [fibonacciBraidGroupHom_sigmaOne]
  rfl

@[simp]
theorem fibonacciBraidRepresentation_sigmaTwo
    (q : Units ℂ) (τ s : ℂ)
    (hq_inv : (q ^ (-4 : ℤ) : ℂ) = - (q : ℂ))
    (hq_pow3 : (q ^ (3 : ℤ) : ℂ) = (q : ℂ) ^ 3)
    (hq5 : (q : ℂ) ^ 5 = -1)
    (h_poly : (q : ℂ) ^ 4 - (q : ℂ) ^ 3 + (q : ℂ) ^ 2 -
      (q : ℂ) + 1 = 0)
    (hτq : τ = (q : ℂ) ^ 2 - (q : ℂ) ^ 3)
    (hs : s ^ 2 = τ)
    (hτ : τ ^ 2 + τ = 1) :
    fibonacciBraidRepresentation q τ s hq_inv hq_pow3 hq5 h_poly hτq hs hτ sigmaTwo =
      bLinearMap q τ s := by
  change
    (fibonacciBraidGroupHom q τ s hq_inv hq_pow3 hq5 h_poly hτq hs hτ sigmaTwo).toLinearMap =
      bLinearMap q τ s
  rw [fibonacciBraidGroupHom_sigmaTwo]
  rfl

end InfoGeometry.Categorical.FibonacciBraidGroup3Representation
