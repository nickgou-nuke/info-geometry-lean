import InfoGeometry.Categorical.FibonacciTwoSidedBraid
import InfoGeometry.Canonical.SplitOctonionChiralPhaseSpace

/-!
# Polarized two-sheet Fibonacci braid action

This module packages the already-proved two-sided Fibonacci braid generators on
a pair of chiral sheets. Algebraically, the positive sheet is acted on by a
signed generator `g`, while the negative sheet is acted on by the inverse
orientation `g⁻¹`.

This is deliberately not called a topological fibration theorem: no total
space/base-space map, fiber, local trivialization, Fadell--Neuwirth sequence,
Garside localization, or Hopf fibration is asserted here.

The split-octonion mixed upper/lower product is recorded separately as the
native chiral pairing. It is not identified with an Ore localization map.
-/

namespace InfoGeometry.QuantumAlgebra.PolarizedBraidFibration

open InfoGeometry.Algebra
open InfoGeometry.Algebra.ZornMatrix
open InfoGeometry.Canonical.SplitOctonionChiralPhaseSpace
open InfoGeometry.Categorical.FibonacciFusionTreeLinearEquiv
open InfoGeometry.Categorical.FibonacciTwoSidedBraid

/-- Two copies of the finite Fibonacci fusion-tree carrier, interpreted as
positive and negative chiral sheets. -/
abbrev PolarizedFusionTree := FusionTree × FusionTree

/-- Swap the two chiral sheets. -/
def sheetSwap (z : PolarizedFusionTree) : PolarizedFusionTree := (z.2, z.1)

@[simp] theorem sheetSwap_involutive (z : PolarizedFusionTree) :
    sheetSwap (sheetSwap z) = z := by
  rcases z with ⟨z₊, z₋⟩
  rfl

/-- A signed braid generator acts with opposite orientation on the two sheets:
`g` on the positive sheet and `g⁻¹` on the negative sheet. -/
noncomputable def polarizedGeneratorAction
    (q : Units ℂ) (τ s : ℂ)
    (hs : s ^ 2 = τ) (hτ : τ ^ 2 + τ = 1)
    (g : SignedGenerator) (z : PolarizedFusionTree) : PolarizedFusionTree :=
  (evalGenerator q τ s hs hτ g z.1,
    evalGenerator q τ s hs hτ g.inv z.2)

/-- Applying the inverse signed generator cancels the polarized action on both
sheets. -/
theorem polarizedGeneratorAction_inverse
    (q : Units ℂ) (τ s : ℂ)
    (hs : s ^ 2 = τ) (hτ : τ ^ 2 + τ = 1)
    (g : SignedGenerator) (z : PolarizedFusionTree) :
    polarizedGeneratorAction q τ s hs hτ g.inv
        (polarizedGeneratorAction q τ s hs hτ g z) = z := by
  rcases z with ⟨z₊, z₋⟩
  apply Prod.ext
  · simp only [polarizedGeneratorAction]
    rw [evalGenerator_inv]
    exact LinearEquiv.symm_apply_apply _ _
  · simp only [polarizedGeneratorAction, SignedGenerator.inv_inv]
    rw [evalGenerator_inv]
    exact LinearEquiv.apply_symm_apply _ _

/-- Swapping the two sheets intertwines the action of `g` with the action of
its inverse orientation. -/
theorem sheetSwap_intertwines_inverse
    (q : Units ℂ) (τ s : ℂ)
    (hs : s ^ 2 = τ) (hτ : τ ^ 2 + τ = 1)
    (g : SignedGenerator) (z : PolarizedFusionTree) :
    sheetSwap (polarizedGeneratorAction q τ s hs hτ g z) =
      polarizedGeneratorAction q τ s hs hτ g.inv (sheetSwap z) := by
  rcases z with ⟨z₊, z₋⟩
  simp [sheetSwap, polarizedGeneratorAction, SignedGenerator.inv_inv]

/-- The mixed split-octonion upper/lower product is the native chiral pairing.
This is the algebraic contraction between the two Peirce sheets. -/
theorem mixed_sheet_pairing (q p : Vec) :
    upperZorn q * lowerZorn p = chiralPairing q p • (E11 : Carrier) :=
  upperZorn_mul_lowerZorn q p

/-- On circular basis vectors the mixed-sheet scalar readout is Kronecker
orthogonality. -/
theorem mixed_basis_pairing (i j : Fin 3) :
    (upperZorn (Vec3.basis i) * lowerZorn (Vec3.basis j)).a =
      if i = j then 1 else 0 := by
  rw [upperZorn_mul_lowerZorn]
  fin_cases i <;> fin_cases j <;>
    simp [chiralPairing, Vec3.dot, Vec3.basis, ZornMatrix.smul, E11]

end InfoGeometry.QuantumAlgebra.PolarizedBraidFibration
