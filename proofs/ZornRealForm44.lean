import proofs.CanonicalZornRealSpin44
import Mathlib.Algebra.Star.Basic

/-!
# Real Form and Conjugation of the Zorn Clifford Algebra

This module defines the canonical real involution (complex conjugation) on the
complex Zorn vector space. We prove that the fixed points of this involution
exactly correspond to the real split (4,4) signature carrier `RealSplit44`
defined in `CanonicalZornRealSpin44.lean`.

This formally isolates the $C\ell(4,4)$ Lorentz/Split real form from the 
complexified $C\ell_8(\mathbb{C})$ Clifford algebra, demonstrating that the
historical SageMath basis natively generates the physical real split signature.
-/

noncomputable section

namespace ZornRealForm44

open CanonicalZornRealSpin44
open CanonicalZornCompositionTriality
open CanonicalZornCliffordRepresentation

/-! ## Real Involution on Coordinates -/

/-- Complex conjugation on `Fin 8 → ℂ` -/
def coordRealInvolution : (Fin 8 → ℂ) →ₗ[ℝ] (Fin 8 → ℂ) where
  toFun v := fun i => starRingEnd ℂ (v i)
  map_add' x y := by funext i; exact map_add _ (x i) (y i)
  map_smul' c x := by
    funext i
    change starRingEnd ℂ (c • x i) = c • starRingEnd ℂ (x i)
    simp

theorem coordRealInvolution_apply (v : Fin 8 → ℂ) (i : Fin 8) :
    coordRealInvolution v i = starRingEnd ℂ (v i) :=
  rfl

theorem coordRealInvolution_involutive (v : Fin 8 → ℂ) :
    coordRealInvolution (coordRealInvolution v) = v := by
  funext i
  simp [coordRealInvolution_apply]

/-! ## Fixed points match RealSplit44 -/

/-- The image of `realSplit44Coordinates` is fixed by `coordRealInvolution`. -/
theorem realSplit44Coordinates_fixed (x : RealSplit44) :
    coordRealInvolution (realSplit44Coordinates x) = realSplit44Coordinates x := by
  funext i
  simp only [coordRealInvolution_apply]
  fin_cases i <;>
    simp [realSplit44Coordinates]

/-- Complex conjugation over the Zorn vector copy `Vector8` -/
def zornRealInvolution : Vector8 →ₗ[ℝ] Vector8 :=
  (((copyLinearEquivCoordinates TrialitySector.vector).symm).restrictScalars ℝ).toLinearMap.comp
    (coordRealInvolution.comp
      (((copyLinearEquivCoordinates TrialitySector.vector).restrictScalars ℝ).toLinearMap))

/-- The canonical embedding of `RealSplit44` is exactly the fixed-point real form
of the `Vector8` representation space. -/
theorem realSplit44ToVector8_fixed (x : RealSplit44) :
    zornRealInvolution (realSplit44ToVector8 x) = realSplit44ToVector8 x := by
  dsimp [zornRealInvolution, realSplit44ToVector8]
  simp [realSplit44Coordinates_fixed]

end ZornRealForm44

end noncomputable section
