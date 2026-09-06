import Mathlib.LinearAlgebra.GeneralLinearGroup.Basic
import Mathlib.RepresentationTheory.Basic
import InfoGeometry.Categorical.BraidThreePresentedGroup
import InfoGeometry.Categorical.FibonacciFusionTreeBraiding

/-!
# Fibonacci representation of the presented three-strand braid group

This file promotes the existing finite Fibonacci generators

* `R = rLinearEquiv q`,
* `B = bLinearEquiv q τ s hs hτ`,

to a genuine homomorphism from the presented braid group `B₃`.  The Artin
relation is discharged by the already-proved finite fusion-tree matrix identity.

The resulting `Representation ℂ BraidGroup3 FusionTree` contains inverse braid
orientation automatically through the group inverse.  No Garside normal-form,
Weyl-group quotient, topological fibration, or CPT identification is asserted.
-/

namespace InfoGeometry.Categorical.FibonacciBraidGroupRepresentation

open InfoGeometry.Categorical.BraidThreePresentedGroup
open InfoGeometry.Categorical.FibonacciFusionTreeLinearEquiv
open InfoGeometry.Categorical.FibonacciFusionTreeBraiding

/-- The general linear group of the two-channel Fibonacci fusion-tree space. -/
abbrev FusionTreeGL :=
  LinearMap.GeneralLinearGroup ℂ FusionTree

/-- The first Fibonacci braid generator as an element of the general linear
group. -/
noncomputable def fibonacciSigmaOne (q : Units ℂ) : FusionTreeGL :=
  LinearMap.GeneralLinearGroup.ofLinearEquiv (rLinearEquiv q)

/-- The second Fibonacci braid generator `B = F R F` as an element of the
general linear group. -/
noncomputable def fibonacciSigmaTwo
    (q : Units ℂ) (τ s : ℂ)
    (hs : s ^ 2 = τ) (hτ : τ ^ 2 + τ = 1) : FusionTreeGL :=
  LinearMap.GeneralLinearGroup.ofLinearEquiv
    (bLinearEquiv q τ s hs hτ)

/-- The finite Fibonacci linear equivalences satisfy the Artin relation. -/
theorem fibonacciLinearEquiv_artin
    (q : Units ℂ) (τ s : ℂ)
    (hs : s ^ 2 = τ) (hτ : τ ^ 2 + τ = 1)
    (hq_inv : (q ^ (-4 : ℤ) : ℂ) = - (q : ℂ))
    (hq_pow3 : (q ^ (3 : ℤ) : ℂ) = (q : ℂ) ^ 3)
    (hq5 : (q : ℂ) ^ 5 = -1)
    (h_poly : (q : ℂ) ^ 4 - (q : ℂ) ^ 3 + (q : ℂ) ^ 2 -
      (q : ℂ) + 1 = 0)
    (hτq : τ = (q : ℂ) ^ 2 - (q : ℂ) ^ 3) :
    rLinearEquiv q * bLinearEquiv q τ s hs hτ * rLinearEquiv q =
      bLinearEquiv q τ s hs hτ * rLinearEquiv q *
        bLinearEquiv q τ s hs hτ := by
  apply LinearEquiv.ext
  intro x
  change
    (((rLinearMap q).comp (bLinearMap q τ s)).comp (rLinearMap q)) x =
      (((bLinearMap q τ s).comp (rLinearMap q)).comp
        (bLinearMap q τ s)) x
  exact congrArg
    (fun f : Module.End ℂ FusionTree => f x)
    (fusionTree_artin q τ s hq_inv hq_pow3 hq5 h_poly hτq hs)

/-- The Fibonacci generators form an Artin pair in the fusion-tree general
linear group. -/
noncomputable def fibonacciArtinPair
    (q : Units ℂ) (τ s : ℂ)
    (hs : s ^ 2 = τ) (hτ : τ ^ 2 + τ = 1)
    (hq_inv : (q ^ (-4 : ℤ) : ℂ) = - (q : ℂ))
    (hq_pow3 : (q ^ (3 : ℤ) : ℂ) = (q : ℂ) ^ 3)
    (hq5 : (q : ℂ) ^ 5 = -1)
    (h_poly : (q : ℂ) ^ 4 - (q : ℂ) ^ 3 + (q : ℂ) ^ 2 -
      (q : ℂ) + 1 = 0)
    (hτq : τ = (q : ℂ) ^ 2 - (q : ℂ) ^ 3) :
    ArtinPair FusionTreeGL where
  sigmaOne := fibonacciSigmaOne q
  sigmaTwo := fibonacciSigmaTwo q τ s hs hτ
  artin := by
    apply Units.ext
    change
      ((rLinearMap q).comp (bLinearMap q τ s)).comp (rLinearMap q) =
        ((bLinearMap q τ s).comp (rLinearMap q)).comp
          (bLinearMap q τ s)
    exact fusionTree_artin q τ s hq_inv hq_pow3 hq5 h_poly hτq hs

/-- The genuine `B₃` action by invertible Fibonacci fusion-tree operators. -/
noncomputable def fibonacciBraidGroupHom
    (q : Units ℂ) (τ s : ℂ)
    (hs : s ^ 2 = τ) (hτ : τ ^ 2 + τ = 1)
    (hq_inv : (q ^ (-4 : ℤ) : ℂ) = - (q : ℂ))
    (hq_pow3 : (q ^ (3 : ℤ) : ℂ) = (q : ℂ) ^ 3)
    (hq5 : (q : ℂ) ^ 5 = -1)
    (h_poly : (q : ℂ) ^ 4 - (q : ℂ) ^ 3 + (q : ℂ) ^ 2 -
      (q : ℂ) + 1 = 0)
    (hτq : τ = (q : ℂ) ^ 2 - (q : ℂ) ^ 3) :
    BraidGroup3 →* FusionTreeGL :=
  (fibonacciArtinPair q τ s hs hτ hq_inv hq_pow3 hq5 h_poly hτq).toBraidGroupHom

@[simp]
theorem fibonacciBraidGroupHom_sigmaOne
    (q : Units ℂ) (τ s : ℂ)
    (hs : s ^ 2 = τ) (hτ : τ ^ 2 + τ = 1)
    (hq_inv : (q ^ (-4 : ℤ) : ℂ) = - (q : ℂ))
    (hq_pow3 : (q ^ (3 : ℤ) : ℂ) = (q : ℂ) ^ 3)
    (hq5 : (q : ℂ) ^ 5 = -1)
    (h_poly : (q : ℂ) ^ 4 - (q : ℂ) ^ 3 + (q : ℂ) ^ 2 -
      (q : ℂ) + 1 = 0)
    (hτq : τ = (q : ℂ) ^ 2 - (q : ℂ) ^ 3) :
    fibonacciBraidGroupHom q τ s hs hτ hq_inv hq_pow3 hq5 h_poly hτq
        sigmaOne =
      fibonacciSigmaOne q := by
  exact ArtinPair.toBraidGroupHom_sigmaOne _

@[simp]
theorem fibonacciBraidGroupHom_sigmaTwo
    (q : Units ℂ) (τ s : ℂ)
    (hs : s ^ 2 = τ) (hτ : τ ^ 2 + τ = 1)
    (hq_inv : (q ^ (-4 : ℤ) : ℂ) = - (q : ℂ))
    (hq_pow3 : (q ^ (3 : ℤ) : ℂ) = (q : ℂ) ^ 3)
    (hq5 : (q : ℂ) ^ 5 = -1)
    (h_poly : (q : ℂ) ^ 4 - (q : ℂ) ^ 3 + (q : ℂ) ^ 2 -
      (q : ℂ) + 1 = 0)
    (hτq : τ = (q : ℂ) ^ 2 - (q : ℂ) ^ 3) :
    fibonacciBraidGroupHom q τ s hs hτ hq_inv hq_pow3 hq5 h_poly hτq
        sigmaTwo =
      fibonacciSigmaTwo q τ s hs hτ := by
  exact ArtinPair.toBraidGroupHom_sigmaTwo _

/-- The Mathlib-native linear representation associated to the invertible
Fibonacci braid action. -/
noncomputable def fibonacciBraidRepresentation
    (q : Units ℂ) (τ s : ℂ)
    (hs : s ^ 2 = τ) (hτ : τ ^ 2 + τ = 1)
    (hq_inv : (q ^ (-4 : ℤ) : ℂ) = - (q : ℂ))
    (hq_pow3 : (q ^ (3 : ℤ) : ℂ) = (q : ℂ) ^ 3)
    (hq5 : (q : ℂ) ^ 5 = -1)
    (h_poly : (q : ℂ) ^ 4 - (q : ℂ) ^ 3 + (q : ℂ) ^ 2 -
      (q : ℂ) + 1 = 0)
    (hτq : τ = (q : ℂ) ^ 2 - (q : ℂ) ^ 3) :
    Representation ℂ BraidGroup3 FusionTree :=
  (Units.coeHom (Module.End ℂ FusionTree)).comp
    (fibonacciBraidGroupHom q τ s hs hτ hq_inv hq_pow3 hq5 h_poly hτq)

@[simp]
theorem fibonacciBraidRepresentation_sigmaOne
    (q : Units ℂ) (τ s : ℂ)
    (hs : s ^ 2 = τ) (hτ : τ ^ 2 + τ = 1)
    (hq_inv : (q ^ (-4 : ℤ) : ℂ) = - (q : ℂ))
    (hq_pow3 : (q ^ (3 : ℤ) : ℂ) = (q : ℂ) ^ 3)
    (hq5 : (q : ℂ) ^ 5 = -1)
    (h_poly : (q : ℂ) ^ 4 - (q : ℂ) ^ 3 + (q : ℂ) ^ 2 -
      (q : ℂ) + 1 = 0)
    (hτq : τ = (q : ℂ) ^ 2 - (q : ℂ) ^ 3) :
    fibonacciBraidRepresentation q τ s hs hτ hq_inv hq_pow3 hq5 h_poly hτq
        sigmaOne =
      rLinearMap q := by
  change
    ((fibonacciBraidGroupHom q τ s hs hτ hq_inv hq_pow3 hq5 h_poly hτq
      sigmaOne : FusionTreeGL) : Module.End ℂ FusionTree) = rLinearMap q
  rw [fibonacciBraidGroupHom_sigmaOne]
  rfl

@[simp]
theorem fibonacciBraidRepresentation_sigmaTwo
    (q : Units ℂ) (τ s : ℂ)
    (hs : s ^ 2 = τ) (hτ : τ ^ 2 + τ = 1)
    (hq_inv : (q ^ (-4 : ℤ) : ℂ) = - (q : ℂ))
    (hq_pow3 : (q ^ (3 : ℤ) : ℂ) = (q : ℂ) ^ 3)
    (hq5 : (q : ℂ) ^ 5 = -1)
    (h_poly : (q : ℂ) ^ 4 - (q : ℂ) ^ 3 + (q : ℂ) ^ 2 -
      (q : ℂ) + 1 = 0)
    (hτq : τ = (q : ℂ) ^ 2 - (q : ℂ) ^ 3) :
    fibonacciBraidRepresentation q τ s hs hτ hq_inv hq_pow3 hq5 h_poly hτq
        sigmaTwo =
      bLinearMap q τ s := by
  change
    ((fibonacciBraidGroupHom q τ s hs hτ hq_inv hq_pow3 hq5 h_poly hτq
      sigmaTwo : FusionTreeGL) : Module.End ℂ FusionTree) = bLinearMap q τ s
  rw [fibonacciBraidGroupHom_sigmaTwo]
  rfl

/-- Negative braid orientation is automatically the inverse action in the same
group representation. -/
@[simp]
theorem sigmaOne_inverse_cancellation
    (q : Units ℂ) (τ s : ℂ)
    (hs : s ^ 2 = τ) (hτ : τ ^ 2 + τ = 1)
    (hq_inv : (q ^ (-4 : ℤ) : ℂ) = - (q : ℂ))
    (hq_pow3 : (q ^ (3 : ℤ) : ℂ) = (q : ℂ) ^ 3)
    (hq5 : (q : ℂ) ^ 5 = -1)
    (h_poly : (q : ℂ) ^ 4 - (q : ℂ) ^ 3 + (q : ℂ) ^ 2 -
      (q : ℂ) + 1 = 0)
    (hτq : τ = (q : ℂ) ^ 2 - (q : ℂ) ^ 3)
    (x : FusionTree) :
    fibonacciBraidRepresentation q τ s hs hτ hq_inv hq_pow3 hq5 h_poly hτq
        sigmaOne⁻¹
      (fibonacciBraidRepresentation q τ s hs hτ hq_inv hq_pow3 hq5 h_poly hτq
        sigmaOne x) = x := by
  exact Representation.inv_self_apply
    (fibonacciBraidRepresentation q τ s hs hτ hq_inv hq_pow3 hq5 h_poly hτq)
    sigmaOne x

/-- The represented Garside half-twist is the expected `R B R` operator.
No Weyl-group or sheet-swap identification is asserted here. -/
theorem fibonacciBraidRepresentation_garsideDelta
    (q : Units ℂ) (τ s : ℂ)
    (hs : s ^ 2 = τ) (hτ : τ ^ 2 + τ = 1)
    (hq_inv : (q ^ (-4 : ℤ) : ℂ) = - (q : ℂ))
    (hq_pow3 : (q ^ (3 : ℤ) : ℂ) = (q : ℂ) ^ 3)
    (hq5 : (q : ℂ) ^ 5 = -1)
    (h_poly : (q : ℂ) ^ 4 - (q : ℂ) ^ 3 + (q : ℂ) ^ 2 -
      (q : ℂ) + 1 = 0)
    (hτq : τ = (q : ℂ) ^ 2 - (q : ℂ) ^ 3) :
    fibonacciBraidRepresentation q τ s hs hτ hq_inv hq_pow3 hq5 h_poly hτq
        garsideDelta =
      ((rLinearMap q).comp (bLinearMap q τ s)).comp (rLinearMap q) := by
  change
    fibonacciBraidRepresentation q τ s hs hτ hq_inv hq_pow3 hq5 h_poly hτq
        (sigmaOne * sigmaTwo * sigmaOne) = _
  rw [map_mul, map_mul]
  rw [fibonacciBraidRepresentation_sigmaOne q τ s hs hτ hq_inv hq_pow3 hq5 h_poly hτq,
    fibonacciBraidRepresentation_sigmaTwo q τ s hs hτ hq_inv hq_pow3 hq5 h_poly hτq]
  rfl

end InfoGeometry.Categorical.FibonacciBraidGroupRepresentation
