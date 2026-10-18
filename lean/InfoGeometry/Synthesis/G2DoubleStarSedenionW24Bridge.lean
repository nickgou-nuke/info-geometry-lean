/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.Lie.G2DoubleStarRootDecomposition
import InfoGeometry.Canonical.CyclotomicOperatorSpine
import InfoGeometry.Synthesis.SplitSedenionDerivationAnomaly
import InfoGeometry.Synthesis.Cl44LeftIdealSplitSedenionSynthesis

/-!
# Finite `G₂` Root-Sheet Enumeration, `Φ₂₄` Reduction, and Split-Doubling Identities

These are separate finite results. The only cross-carrier construction is the explicit
equivalence from the actual `doubleStarIndices` subtype paired with `Fin 2` to `Fin 24`.
No compatibility with a `Φ₂₄` operator action or with the split-sedenion multiplication is
asserted.

This module connects the repository's existing finite `G₂` root-index readout, endomorphism
cyclotomic polynomial identities, and Cayley–Dickson split-doubling equations:

1. **Section 1 (Root-Index Sheet Carrier)**:
   - Uses the actual subtype of `doubleStarIndices` from
     `InfoGeometry.Lie.G2DoubleStarRootDecomposition` and proves that this carrier paired with
     `Fin 2` is equivalent to `Fin 24`. This is a finite carrier equivalence only; it defines no
     action and no intertwiner with the cyclotomic endomorphism or split-sedenion product.
2. **Section 2 (Endomorphism Cyclotomic Doubling `Φ₂₄(T) = Φ₁₂(T²)` and Sheet-Swap Lift)**:
   - Proves the operator polynomial identity `phi24Eval T = phi12Eval (T ^ 2)` on any complex
     module endomorphism `T : Module.End ℂ V` from `InfoGeometry.Canonical.CyclotomicOperatorSpine`.
   - Defines the off-diagonal sheet-swap lift `sheetSwapLift A : Module.End ℂ (V × V)` mapping
     `(v₁, v₂) ↦ (A v₂, A v₁)` and proves that its square acts diagonally as `(A² v₁, A² v₂)`.
3. **Section 3 (Paired Split-Doubling Square-Zero Rays and Null-Norm Cancellation)**:
   - Proves that for any split imaginary unit `u` (`u * u = 1`, `starA u = -u`, `starA 1 = 1`),
     both sheet pairs `(u, 1)` and `(u, -1)` have square zero under `cdMul starA (-1)`, and any
     lifted star-derivation `cdLift D₀` preserves the first-order zero-product tangent relation.
   - Proves that on `SplitSedenion R`, both diagonal pairs `(x, x)` and `(x, -x)` have
     `sedenionNorm = 0`.
-/

noncomputable section

namespace InfoGeometry.Synthesis.G2DoubleStarSedenionW24Bridge

open InfoGeometry.Lie.CanonicalZornCartanAdjointRootDecomposition
open InfoGeometry.Lie.G2DoubleStarRootDecomposition
open InfoGeometry.Canonical.CyclotomicOperatorSpine
open InfoGeometry.Synthesis.SplitSedenionDerivationAnomaly
open InfoGeometry.Synthesis.Cl44LeftIdealSplitSedenionSynthesis
open InfoGeometry.Canonical.ZornSplitOctonionFin8Bridge
open InfoGeometry.Canonical.SplitOctonionParaKahlerNullCone

/-! ## Section 1: Root-Index Sheet Carrier -/

/-- The actual `G₂` nonzero-root index subtype paired with a two-sheet label. -/
abbrev DoubleStarSheetCarrier := {i : Fin 14 // i ∈ doubleStarIndices} × Fin 2

/-- The 12 native double-star root indices and two sheet labels give a 24-element carrier. -/
theorem doubleStarSheetCarrier_card : Fintype.card DoubleStarSheetCarrier = 24 := by
  simp [DoubleStarSheetCarrier, Fintype.card_coe, doubleStarIndices_card]

/-- Enumeration of the actual root-index/sheet carrier by 24 finite labels.
The equivalence preserves only finite carrier cardinality; no operator action is transported. -/
noncomputable def doubleStarSheetCarrierEquivFin24 : DoubleStarSheetCarrier ≃ Fin 24 :=
  Fintype.equivFinOfCardEq doubleStarSheetCarrier_card

/-! ## Section 2: Endomorphism Cyclotomic Reduction `Φ₂₄(T) = Φ₁₂(T²)` and Sheet-Swap Lift -/

section EndomorphismCyclotomic

variable {V : Type*} [AddCommGroup V] [Module ℂ V]

/-- For any endomorphism `T : Module.End ℂ V`, evaluating `Φ₂₄(T) = T⁸ - T⁴ + 1` is identically
equal to evaluating `Φ₁₂(X) = X⁴ - X² + 1` at `T²`. -/
theorem phi24Eval_eq_phi12Eval_sq (T : Module.End ℂ V) :
    phi24Eval T = phi12Eval (T ^ 2) := by
  unfold phi24Eval phi12Eval
  noncomm_ring

/-- Consequently, any endomorphism whose square is annihilated by `phi12Eval` is annihilated by
`phi24Eval`. -/
theorem phi24Eval_eq_zero_of_phi12Eval_sq_eq_zero (T : Module.End ℂ V)
    (hT : phi12Eval (T ^ 2) = 0) :
    phi24Eval T = 0 := by
  rw [phi24Eval_eq_phi12Eval_sq T, hT]

/-- Off-diagonal sheet-swap lift of an endomorphism `A : Module.End ℂ V` to `V × V`,
acting by `(v₁, v₂) ↦ (A v₂, A v₁)`. -/
def sheetSwapLift (A : Module.End ℂ V) : Module.End ℂ (V × V) :=
  { toFun := fun v => (A v.2, A v.1)
    map_add' := by intro v w; simp
    map_smul' := by intro c v; simp }

/-- The square of `sheetSwapLift A` acts diagonally on the two sheets as `(A² v₁, A² v₂)`. -/
theorem sheetSwapLift_sq_apply (A : Module.End ℂ V) (v : V × V) :
    ((sheetSwapLift A) ^ 2) v = ((A ^ 2) v.1, (A ^ 2) v.2) := by
  change sheetSwapLift A (sheetSwapLift A v) = (A (A v.1), A (A v.2))
  rfl

end EndomorphismCyclotomic

/-! ## Section 3: Paired Split-Doubling Square-Zero Rays and Null-Norm Cancellation -/

/-- For an element `u` satisfying `u * u = 1`, `starA u = -u`, and `starA 1 = 1`, both opposite
sheet combinations `(u, 1)` and `(u, -1)` have square zero under `cdMul starA (-1)`. -/
theorem split_cayleyDickson_plus_minus_square_zero
    {R A : Type*} [CommRing R] [NonAssocRing A] [Module R A]
    (starA : A → A) (u : A)
    (h_star_one : starA 1 = 1)
    (h_star_neg_one : starA (-1 : A) = -1)
    (h_u_sq : u * u = 1)
    (h_u_star : starA u = -u) :
    cdMul starA (-1 : R) (u, (1 : A)) (u, (1 : A)) = (0, 0) ∧
    cdMul starA (-1 : R) (u, (-1 : A)) (u, (-1 : A)) = (0, 0) := by
  refine ⟨split_cayleyDickson_square_zero starA u h_star_one h_u_sq h_u_star, ?_⟩
  ext
  · dsimp [cdMul]
    rw [h_u_sq, h_star_neg_one, neg_mul_neg, mul_one, neg_one_smul, add_neg_cancel]
  · dsimp [cdMul]
    rw [neg_one_mul, h_u_star, neg_one_mul, neg_neg, neg_add_cancel]

/-- Any diagonally lifted star-derivation `cdLift D₀` maps a square-zero element `z` of
`cdMul starA γ` into the first-order tangent equation
`cdMul (cdLift D₀ z) z + cdMul z (cdLift D₀ z) = (0, 0)`. -/
theorem cdLift_preserves_square_zero_tangent
    {R A : Type*} [CommRing R] [NonUnitalNonAssocRing A] [Module R A]
    [IsScalarTower R A A] [SMulCommClass R A A]
    (starA : A → A) (γ : R) (D₀ : A → A)
    (hD : IsStarDerivation R starA D₀)
    {z : A × A} (hz : cdMul starA γ z z = (0, 0)) :
    cdMul starA γ (cdLift D₀ z) z + cdMul starA γ z (cdLift D₀ z) = (0, 0) := by
  have hleib := (cdLift_is_cayleyDickson_star_derivation starA γ D₀ hD z z).1
  have h0 : D₀ 0 = 0 := by
    have hadd := hD.1 0 0
    have hadd' : D₀ 0 + 0 = D₀ 0 + D₀ 0 := by simpa using hadd
    exact (add_left_cancel hadd').symm
  have hlift0 : cdLift D₀ (0, 0) = ((0 : A), (0 : A)) := by
    ext <;> exact h0
  rw [hz, hlift0] at hleib
  exact hleib.symm

/-- On `SplitSedenion R`, both diagonal pairs `(x, x)` and `(x, -x)` have vanishing
`sedenionNorm`. -/
theorem sedenion_plus_minus_diagonal_norm_zero {R : Type*} [CommRing R]
    (x : ZornSplitOctonion R) :
    sedenionNorm (x, x) = 0 ∧ sedenionNorm (x, zornSmul (-1) x) = 0 := by
  constructor
  · simp [sedenionNorm]
  · dsimp [sedenionNorm, zornNorm, zornSmul, vec3Dot]
    ring

end InfoGeometry.Synthesis.G2DoubleStarSedenionW24Bridge
