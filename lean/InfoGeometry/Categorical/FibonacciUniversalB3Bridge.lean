import InfoGeometry.Categorical.UniversalArtinBraidRepresentation
import InfoGeometry.Categorical.FibonacciBraidGroup3Representation
import InfoGeometry.Categorical.BraidGroup3PresentationBridge

/-!
# Fibonacci B₃ representation through the universal Artin engine

This module migrates the already-verified Fibonacci braid representation onto
the canonical finite braid-group owner `Braid.braid_group 3`.

The existing finite operators
  * `rLinearEquiv q`,
  * `bLinearEquiv q τ s hs hτ`
already satisfy the Artin relation by `fusionTree_artin_equiv`.

We package them as an `ArtinBraidSystem ... 2`, obtain the universal
homomorphism from `Braid.braid_group 3`, and prove that it agrees with the
legacy bespoke `fibonacciBraidGroupHom` after transport across the canonical
presentation equivalence.

No new Fibonacci identities are proved here.
-/

noncomputable section

namespace InfoGeometry.Categorical.FibonacciUniversalB3Bridge

open Braid
open InfoGeometry.Categorical.UniversalArtinBraidRepresentation
open InfoGeometry.Categorical.FibonacciBraidGroup3Representation
open InfoGeometry.Categorical.FibonacciFusionTreeBraiding
open InfoGeometry.Categorical.FibonacciFusionTreeLinearEquiv
open InfoGeometry.Categorical.BraidGroup3PresentationBridge

abbrev FibAut := FusionTree ≃ₗ[ℂ] FusionTree

/-- The verified Fibonacci R and FRF operators as a universal Artin system. -/
def fibonacciArtinSystem
    (q : Units ℂ) (τ s : ℂ)
    (hq_inv : (q ^ (-4 : ℤ) : ℂ) = - (q : ℂ))
    (hq_pow3 : (q ^ (3 : ℤ) : ℂ) = (q : ℂ) ^ 3)
    (hq5 : (q : ℂ) ^ 5 = -1)
    (h_poly : (q : ℂ) ^ 4 - (q : ℂ) ^ 3 + (q : ℂ) ^ 2 -
      (q : ℂ) + 1 = 0)
    (hτq : τ = (q : ℂ) ^ 2 - (q : ℂ) ^ 3)
    (hs : s ^ 2 = τ)
    (hτ : τ ^ 2 + τ = 1) :
    ArtinBraidSystem FibAut 2 where
  gen i := if i = 0 then rLinearEquiv q else bLinearEquiv q τ s hs hτ
  adjacent i j hij := by
    fin_cases i <;> fin_cases j
    · omega
    · simpa using
        fusionTree_artin_equiv q τ s hq_inv hq_pow3 hq5 h_poly hτq hs hτ
    · omega
    · omega
  farCommute i j hij := by
    fin_cases i <;> fin_cases j <;> omega

/-- Universal Fibonacci representation on the canonical `Braid.braid_group 3`. -/
def fibonacciUniversalB3Hom
    (q : Units ℂ) (τ s : ℂ)
    (hq_inv : (q ^ (-4 : ℤ) : ℂ) = - (q : ℂ))
    (hq_pow3 : (q ^ (3 : ℤ) : ℂ) = (q : ℂ) ^ 3)
    (hq5 : (q : ℂ) ^ 5 = -1)
    (h_poly : (q : ℂ) ^ 4 - (q : ℂ) ^ 3 + (q : ℂ) ^ 2 -
      (q : ℂ) + 1 = 0)
    (hτq : τ = (q : ℂ) ^ 2 - (q : ℂ) ^ 3)
    (hs : s ^ 2 = τ)
    (hτ : τ ^ 2 + τ = 1) :
    braid_group 3 →* FibAut :=
  (fibonacciArtinSystem q τ s hq_inv hq_pow3 hq5 h_poly hτq hs hτ).toGroupHom

@[simp] theorem fibonacciUniversalB3Hom_sigma0
    (q : Units ℂ) (τ s : ℂ)
    (hq_inv : (q ^ (-4 : ℤ) : ℂ) = - (q : ℂ))
    (hq_pow3 : (q ^ (3 : ℤ) : ℂ) = (q : ℂ) ^ 3)
    (hq5 : (q : ℂ) ^ 5 = -1)
    (h_poly : (q : ℂ) ^ 4 - (q : ℂ) ^ 3 + (q : ℂ) ^ 2 -
      (q : ℂ) + 1 = 0)
    (hτq : τ = (q : ℂ) ^ 2 - (q : ℂ) ^ 3)
    (hs : s ^ 2 = τ)
    (hτ : τ ^ 2 + τ = 1) :
    fibonacciUniversalB3Hom q τ s hq_inv hq_pow3 hq5 h_poly hτq hs hτ
        (σ' 2 (0 : Fin 2)) =
      rLinearEquiv q := by
  simpa [fibonacciUniversalB3Hom, fibonacciArtinSystem] using
    ArtinBraidSystem.toGroupHom_generator
      (fibonacciArtinSystem q τ s hq_inv hq_pow3 hq5 h_poly hτq hs hτ)
      (0 : Fin 2)

@[simp] theorem fibonacciUniversalB3Hom_sigma1
    (q : Units ℂ) (τ s : ℂ)
    (hq_inv : (q ^ (-4 : ℤ) : ℂ) = - (q : ℂ))
    (hq_pow3 : (q ^ (3 : ℤ) : ℂ) = (q : ℂ) ^ 3)
    (hq5 : (q : ℂ) ^ 5 = -1)
    (h_poly : (q : ℂ) ^ 4 - (q : ℂ) ^ 3 + (q : ℂ) ^ 2 -
      (q : ℂ) + 1 = 0)
    (hτq : τ = (q : ℂ) ^ 2 - (q : ℂ) ^ 3)
    (hs : s ^ 2 = τ)
    (hτ : τ ^ 2 + τ = 1) :
    fibonacciUniversalB3Hom q τ s hq_inv hq_pow3 hq5 h_poly hτq hs hτ
        (σ' 2 (1 : Fin 2)) =
      bLinearEquiv q τ s hs hτ := by
  simpa [fibonacciUniversalB3Hom, fibonacciArtinSystem] using
    ArtinBraidSystem.toGroupHom_generator
      (fibonacciArtinSystem q τ s hq_inv hq_pow3 hq5 h_poly hτq hs hτ)
      (1 : Fin 2)

/-- The legacy Fibonacci representation transported onto the canonical
`Braid.braid_group 3` presentation. -/
def legacyFibonacciOnBraidProject
    (q : Units ℂ) (τ s : ℂ)
    (hq_inv : (q ^ (-4 : ℤ) : ℂ) = - (q : ℂ))
    (hq_pow3 : (q ^ (3 : ℤ) : ℂ) = (q : ℂ) ^ 3)
    (hq5 : (q : ℂ) ^ 5 = -1)
    (h_poly : (q : ℂ) ^ 4 - (q : ℂ) ^ 3 + (q : ℂ) ^ 2 -
      (q : ℂ) + 1 = 0)
    (hτq : τ = (q : ℂ) ^ 2 - (q : ℂ) ^ 3)
    (hs : s ^ 2 = τ)
    (hτ : τ ^ 2 + τ = 1) :
    braid_group 3 →* FibAut :=
  (fibonacciBraidGroupHom q τ s hq_inv hq_pow3 hq5 h_poly hτq hs hτ).comp
    braidProjectToPresentedB3

@[simp] theorem legacyFibonacciOnBraidProject_sigma0
    (q : Units ℂ) (τ s : ℂ)
    (hq_inv : (q ^ (-4 : ℤ) : ℂ) = - (q : ℂ))
    (hq_pow3 : (q ^ (3 : ℤ) : ℂ) = (q : ℂ) ^ 3)
    (hq5 : (q : ℂ) ^ 5 = -1)
    (h_poly : (q : ℂ) ^ 4 - (q : ℂ) ^ 3 + (q : ℂ) ^ 2 -
      (q : ℂ) + 1 = 0)
    (hτq : τ = (q : ℂ) ^ 2 - (q : ℂ) ^ 3)
    (hs : s ^ 2 = τ)
    (hτ : τ ^ 2 + τ = 1) :
    legacyFibonacciOnBraidProject q τ s hq_inv hq_pow3 hq5 h_poly hτq hs hτ
        (σ' 2 (0 : Fin 2)) =
      rLinearEquiv q := by
  simp [legacyFibonacciOnBraidProject]

@[simp] theorem legacyFibonacciOnBraidProject_sigma1
    (q : Units ℂ) (τ s : ℂ)
    (hq_inv : (q ^ (-4 : ℤ) : ℂ) = - (q : ℂ))
    (hq_pow3 : (q ^ (3 : ℤ) : ℂ) = (q : ℂ) ^ 3)
    (hq5 : (q : ℂ) ^ 5 = -1)
    (h_poly : (q : ℂ) ^ 4 - (q : ℂ) ^ 3 + (q : ℂ) ^ 2 -
      (q : ℂ) + 1 = 0)
    (hτq : τ = (q : ℂ) ^ 2 - (q : ℂ) ^ 3)
    (hs : s ^ 2 = τ)
    (hτ : τ ^ 2 + τ = 1) :
    legacyFibonacciOnBraidProject q τ s hq_inv hq_pow3 hq5 h_poly hτq hs hτ
        (σ' 2 (1 : Fin 2)) =
      bLinearEquiv q τ s hs hτ := by
  simp [legacyFibonacciOnBraidProject]

/-- Canary deduplication theorem: after transport to the canonical
`Braid.braid_group 3`, the old bespoke Fibonacci homomorphism is exactly the
universal Artin-system homomorphism. -/
theorem fibonacciUniversalB3Hom_eq_legacy
    (q : Units ℂ) (τ s : ℂ)
    (hq_inv : (q ^ (-4 : ℤ) : ℂ) = - (q : ℂ))
    (hq_pow3 : (q ^ (3 : ℤ) : ℂ) = (q : ℂ) ^ 3)
    (hq5 : (q : ℂ) ^ 5 = -1)
    (h_poly : (q : ℂ) ^ 4 - (q : ℂ) ^ 3 + (q : ℂ) ^ 2 -
      (q : ℂ) + 1 = 0)
    (hτq : τ = (q : ℂ) ^ 2 - (q : ℂ) ^ 3)
    (hs : s ^ 2 = τ)
    (hτ : τ ^ 2 + τ = 1) :
    fibonacciUniversalB3Hom q τ s hq_inv hq_pow3 hq5 h_poly hτq hs hτ =
      legacyFibonacciOnBraidProject q τ s hq_inv hq_pow3 hq5 h_poly hτq hs hτ := by
  symm
  apply ArtinBraidSystem.toGroupHom_unique
    (fibonacciArtinSystem q τ s hq_inv hq_pow3 hq5 h_poly hτq hs hτ)
  intro i
  fin_cases i
  · exact legacyFibonacciOnBraidProject_sigma0
      q τ s hq_inv hq_pow3 hq5 h_poly hτq hs hτ
  · exact legacyFibonacciOnBraidProject_sigma1
      q τ s hq_inv hq_pow3 hq5 h_poly hτq hs hτ

end InfoGeometry.Categorical.FibonacciUniversalB3Bridge
