import InfoGeometry.Categorical.FibonacciFusionTreeBraiding

/-!
# Two-sided Fibonacci braid generators

This module packages the already-proved finite Fibonacci `R` and `B = F R F`
operators together with their inverses.  It is deliberately a generator-level
surface: it does not introduce a second "negative braid monoid", a Garside
localization, a configuration-space fibration, or a Hopf fibration.

The positive generators are represented by `rLinearEquiv q` and
`bLinearEquiv q τ s hs hτ`; the negative generators are their inverse linear
equivalences, realized concretely by replacing `q` with `q⁻¹`.
-/

namespace InfoGeometry.Categorical.FibonacciTwoSidedBraid

open InfoGeometry.Categorical.FibonacciFusionTreeLinearEquiv
open InfoGeometry.Categorical.FibonacciFusionTreeBraiding

/-- The two Artin generators and their formal inverse orientations on the
four-anyon Fibonacci fusion-tree carrier. -/
inductive SignedGenerator where
  | sigma1
  | sigma2
  | sigma1Inv
  | sigma2Inv
  deriving DecidableEq

/-- Formal inversion of a signed generator. -/
def SignedGenerator.inv : SignedGenerator → SignedGenerator
  | .sigma1 => .sigma1Inv
  | .sigma2 => .sigma2Inv
  | .sigma1Inv => .sigma1
  | .sigma2Inv => .sigma2

@[simp] theorem SignedGenerator.inv_inv (g : SignedGenerator) : g.inv.inv = g := by
  cases g <;> rfl

/-- Evaluation of one signed braid generator as an invertible linear operator
on the two-channel Fibonacci fusion-tree space. -/
noncomputable def evalGenerator
    (q : Units ℂ) (τ s : ℂ)
    (hs : s ^ 2 = τ) (hτ : τ ^ 2 + τ = 1) :
    SignedGenerator → (FusionTree ≃ₗ[ℂ] FusionTree)
  | .sigma1 => rLinearEquiv q
  | .sigma2 => bLinearEquiv q τ s hs hτ
  | .sigma1Inv => rLinearEquiv q⁻¹
  | .sigma2Inv => bLinearEquiv q⁻¹ τ s hs hτ

/-- The inverse of the finite `R` equivalence is obtained by replacing `q`
with `q⁻¹`. -/
theorem rLinearEquiv_inverse (q : Units ℂ) :
    (rLinearEquiv q).symm = rLinearEquiv q⁻¹ := by
  ext x
  rfl

/-- Evaluating the formal inverse generator gives the inverse linear
equivalence. -/
theorem evalGenerator_inv
    (q : Units ℂ) (τ s : ℂ)
    (hs : s ^ 2 = τ) (hτ : τ ^ 2 + τ = 1)
    (g : SignedGenerator) :
    evalGenerator q τ s hs hτ g.inv =
      (evalGenerator q τ s hs hτ g).symm := by
  cases g
  · exact (rLinearEquiv_inverse q).symm
  · exact (bLinearEquiv_inverse q τ s hs hτ).symm
  · simpa [SignedGenerator.inv, evalGenerator] using rLinearEquiv_inverse q⁻¹
  · simpa [SignedGenerator.inv, evalGenerator] using
      bLinearEquiv_inverse q⁻¹ τ s hs hτ

/-- Positive and negative orientations of `σ₁` cancel exactly. -/
theorem sigma1_forward_backward
    (q : Units ℂ) (τ s : ℂ)
    (hs : s ^ 2 = τ) (hτ : τ ^ 2 + τ = 1) :
    (evalGenerator q τ s hs hτ .sigma1).trans
        (evalGenerator q τ s hs hτ .sigma1Inv) =
      LinearEquiv.refl ℂ FusionTree := by
  rw [evalGenerator_inv]
  exact LinearEquiv.trans_symm _

/-- Positive and negative orientations of `σ₂` cancel exactly. -/
theorem sigma2_forward_backward
    (q : Units ℂ) (τ s : ℂ)
    (hs : s ^ 2 = τ) (hτ : τ ^ 2 + τ = 1) :
    (evalGenerator q τ s hs hτ .sigma2).trans
        (evalGenerator q τ s hs hτ .sigma2Inv) =
      LinearEquiv.refl ℂ FusionTree := by
  rw [evalGenerator_inv]
  exact LinearEquiv.trans_symm _

/-- Readback of the already-proved positive Artin relation on the two
finite Fibonacci braid generators. -/
theorem positive_artin_relation
    (q : Units ℂ) (τ s : ℂ)
    (hq_inv : (q ^ (-4 : ℤ) : ℂ) = - (q : ℂ))
    (hq_pow3 : (q ^ (3 : ℤ) : ℂ) = (q : ℂ) ^ 3)
    (hq5 : (q : ℂ) ^ 5 = -1)
    (h_poly : (q : ℂ) ^ 4 - (q : ℂ) ^ 3 + (q : ℂ) ^ 2 -
      (q : ℂ) + 1 = 0)
    (hτq : τ = (q : ℂ) ^ 2 - (q : ℂ) ^ 3)
    (hs : s ^ 2 = τ) :
    ((rLinearMap q).comp (bLinearMap q τ s)).comp (rLinearMap q) =
      ((bLinearMap q τ s).comp (rLinearMap q)).comp (bLinearMap q τ s) := by
  exact fusionTree_artin q τ s hq_inv hq_pow3 hq5 h_poly hτq hs

end InfoGeometry.Categorical.FibonacciTwoSidedBraid
