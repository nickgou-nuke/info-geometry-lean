import InfoGeometry.Categorical.FibonacciFusionTreeCategoricalBraiding
import InfoGeometry.Physics.B3PresentedGroup

/-!
# A presented `B₃` representation on the finite Fibonacci fusion-tree carrier

This is a representation-level bridge only.  It uses the existing finite
`R`/`B = F R F` equivalences and the existing Artin theorem; it does not claim
a global `BraidedCategory` instance.
-/

noncomputable section

namespace InfoGeometry.Categorical.FibonacciB3Representation

open InfoGeometry.Categorical.FibonacciFusionTreeBraiding
open InfoGeometry.Categorical.FibonacciFusionTreeLinearEquiv
open InfoGeometry.Physics.B3PresentedGroup

abbrev FibonacciAut := Units (Module.End ℂ FusionTree)

noncomputable def fibonacciUnit
    (e : FusionTree ≃ₗ[ℂ] FusionTree) : FibonacciAut :=
  { val := e.toLinearMap
    inv := e.symm.toLinearMap
    val_inv := by
      ext x
      simp
    inv_val := by
      ext x
      simp }

theorem fibonacci_artin_pair
    (q : Units ℂ) (τ s : ℂ)
    (hq_inv : (q : ℂ) ^ (-4 : ℤ) = - (q : ℂ))
    (hq_pow3 : (q : ℂ) ^ (3 : ℤ) = (q : ℂ) ^ 3)
    (hq5 : (q : ℂ) ^ 5 = -1)
    (h_poly : (q : ℂ) ^ 4 - (q : ℂ) ^ 3 + (q : ℂ) ^ 2 -
      (q : ℂ) + 1 = 0)
    (hτ : τ = (q : ℂ) ^ 2 - (q : ℂ) ^ 3)
    (hs : s ^ 2 = τ)
    (hτ0 : τ ^ 2 + τ = 1) :
    (rLinearEquiv q).trans
        ((bLinearEquiv q τ s hs hτ0).trans (rLinearEquiv q)) =
      (bLinearEquiv q τ s hs hτ0).trans
        ((rLinearEquiv q).trans (bLinearEquiv q τ s hs hτ0)) := by
  exact fusionTree_artin_equiv q τ s hq_inv hq_pow3 hq5 h_poly hτ hs hτ0

def fibonacciB3Representation
    (q : Units ℂ) (τ s : ℂ)
    (hq_inv : (q : ℂ) ^ (-4 : ℤ) = - (q : ℂ))
    (hq_pow3 : (q : ℂ) ^ (3 : ℤ) = (q : ℂ) ^ 3)
    (hq5 : (q : ℂ) ^ 5 = -1)
    (h_poly : (q : ℂ) ^ 4 - (q : ℂ) ^ 3 + (q : ℂ) ^ 2 -
      (q : ℂ) + 1 = 0)
    (hτ : τ = (q : ℂ) ^ 2 - (q : ℂ) ^ 3)
    (hs : s ^ 2 = τ)
    (hτ0 : τ ^ 2 + τ = 1) :
    B3 →* FibonacciAut :=
  homOfArtinPair
    (fibonacciUnit (rLinearEquiv q))
    (fibonacciUnit (bLinearEquiv q τ s hs hτ0))
    (by
      apply Units.ext
      apply LinearMap.ext
      intro x
      simpa [fibonacciUnit, LinearEquiv.trans_apply] using
        congrArg (fun e => e x)
          (fibonacci_artin_pair q τ s hq_inv hq_pow3 hq5 h_poly hτ hs hτ0))

@[simp] theorem fibonacciB3Representation_sig0
    (q : Units ℂ) (τ s : ℂ)
    (hq_inv : (q : ℂ) ^ (-4 : ℤ) = - (q : ℂ))
    (hq_pow3 : (q : ℂ) ^ (3 : ℤ) = (q : ℂ) ^ 3)
    (hq5 : (q : ℂ) ^ 5 = -1)
    (h_poly : (q : ℂ) ^ 4 - (q : ℂ) ^ 3 + (q : ℂ) ^ 2 -
      (q : ℂ) + 1 = 0)
    (hτ : τ = (q : ℂ) ^ 2 - (q : ℂ) ^ 3)
    (hs : s ^ 2 = τ)
    (hτ0 : τ ^ 2 + τ = 1) :
    fibonacciB3Representation q τ s hq_inv hq_pow3 hq5 h_poly hτ hs hτ0
        (PresentedGroup.of B3Gen.sig0 : B3) =
      fibonacciUnit (rLinearEquiv q) := by
  exact homOfArtinPair_sig0 _ _ _

@[simp] theorem fibonacciB3Representation_sig1
    (q : Units ℂ) (τ s : ℂ)
    (hq_inv : (q : ℂ) ^ (-4 : ℤ) = - (q : ℂ))
    (hq_pow3 : (q : ℂ) ^ (3 : ℤ) = (q : ℂ) ^ 3)
    (hq5 : (q : ℂ) ^ 5 = -1)
    (h_poly : (q : ℂ) ^ 4 - (q : ℂ) ^ 3 + (q : ℂ) ^ 2 -
      (q : ℂ) + 1 = 0)
    (hτ : τ = (q : ℂ) ^ 2 - (q : ℂ) ^ 3)
    (hs : s ^ 2 = τ)
    (hτ0 : τ ^ 2 + τ = 1) :
    fibonacciB3Representation q τ s hq_inv hq_pow3 hq5 h_poly hτ hs hτ0
        (PresentedGroup.of B3Gen.sig1 : B3) =
      fibonacciUnit (bLinearEquiv q τ s hs hτ0) := by
  exact homOfArtinPair_sig1 _ _ _

@[simp] theorem fibonacciB3Representation_sig0_inv
    (q : Units ℂ) (τ s : ℂ)
    (hq_inv : (q : ℂ) ^ (-4 : ℤ) = - (q : ℂ))
    (hq_pow3 : (q : ℂ) ^ (3 : ℤ) = (q : ℂ) ^ 3)
    (hq5 : (q : ℂ) ^ 5 = -1)
    (h_poly : (q : ℂ) ^ 4 - (q : ℂ) ^ 3 + (q : ℂ) ^ 2 -
      (q : ℂ) + 1 = 0)
    (hτ : τ = (q : ℂ) ^ 2 - (q : ℂ) ^ 3)
    (hs : s ^ 2 = τ)
    (hτ0 : τ ^ 2 + τ = 1) :
    fibonacciB3Representation q τ s hq_inv hq_pow3 hq5 h_poly hτ hs hτ0
        ((PresentedGroup.of B3Gen.sig0 : B3)⁻¹) =
      (fibonacciUnit (rLinearEquiv q))⁻¹ := by
  rw [map_inv, fibonacciB3Representation_sig0]

@[simp] theorem fibonacciB3Representation_sig1_inv
    (q : Units ℂ) (τ s : ℂ)
    (hq_inv : (q : ℂ) ^ (-4 : ℤ) = - (q : ℂ))
    (hq_pow3 : (q : ℂ) ^ (3 : ℤ) = (q : ℂ) ^ 3)
    (hq5 : (q : ℂ) ^ 5 = -1)
    (h_poly : (q : ℂ) ^ 4 - (q : ℂ) ^ 3 + (q : ℂ) ^ 2 -
      (q : ℂ) + 1 = 0)
    (hτ : τ = (q : ℂ) ^ 2 - (q : ℂ) ^ 3)
    (hs : s ^ 2 = τ)
    (hτ0 : τ ^ 2 + τ = 1) :
    fibonacciB3Representation q τ s hq_inv hq_pow3 hq5 h_poly hτ hs hτ0
        ((PresentedGroup.of B3Gen.sig1 : B3)⁻¹) =
      (fibonacciUnit (bLinearEquiv q τ s hs hτ0))⁻¹ := by
  rw [map_inv, fibonacciB3Representation_sig1]

end InfoGeometry.Categorical.FibonacciB3Representation
