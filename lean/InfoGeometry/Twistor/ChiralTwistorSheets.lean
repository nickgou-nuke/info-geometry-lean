import InfoGeometry.Twistor.RealSplitOctonionCarrierBridge
import Mathlib.Tactic.FinCases

/-!
# Chiral twistor sheets and the Peirce 4+4 polarization

The Penrose twistor carrier is `ℂ² ⊕ ℂ²`.  This owner separates its two
spinor factors and identifies each, as a real four-dimensional vector space,
with one of the two four-dimensional Peirce halves of the established
`1+3+1+3` circular Zorn ordering.

The repository convention is

`u₊ | V₊ | u₋ | V₋`,

so both Peirce halves are stored as `ℝ × ℝ³`: scalar first, then the three
root coordinates.  Abstractly the negative half may equally be written
`V₋ ⊕ ℝ u₋`; no hidden coordinate permutation is introduced here.

No multiplication is defined in this file.  The Zorn coupling is owned by the
native split-octonion multiplication table and is connected in a separate
module.
-/

noncomputable section

namespace InfoGeometry.Twistor.ChiralTwistorSheets

open InfoGeometry.Twistor.PenroseIncidence
open InfoGeometry.Twistor.RealSplitOctonionCarrierBridge
open InfoGeometry.Canonical.SplitOctonionExterior3HodgeDiracBridge

abbrev TwistorPlus := Spinor2
abbrev TwistorMinus := Spinor2
abbrev PeircePlus4 := ℝ × V3
abbrev PeirceMinus4 := ℝ × V3

/-- Real coordinates on a chiral two-component complex spinor, ordered as
`scalar, root₀, root₁, root₂`. -/
def spinor2ToPeirce4 : Spinor2 →ₗ[ℝ] (ℝ × V3) where
  toFun z := ((z 0).re, ![(z 0).im, (z 1).re, (z 1).im])
  map_add' z w := by
    apply Prod.ext
    · simp
    · funext i
      fin_cases i <;> simp
  map_smul' r z := by
    apply Prod.ext
    · simp
    · funext i
      fin_cases i <;> simp

/-- Reconstruct a chiral complex spinor from its four real Peirce coordinates. -/
def peirce4ToSpinor2 : (ℝ × V3) →ₗ[ℝ] Spinor2 where
  toFun q := ![⟨q.1, q.2 0⟩, ⟨q.2 1, q.2 2⟩]
  map_add' q r := by
    funext i
    fin_cases i <;> apply Complex.ext <;> simp
  map_smul' c q := by
    funext i
    fin_cases i <;> apply Complex.ext <;> simp

@[simp] theorem peirce4ToSpinor2_spinor2ToPeirce4 (z : Spinor2) :
    peirce4ToSpinor2 (spinor2ToPeirce4 z) = z := by
  funext i
  fin_cases i <;> apply Complex.ext <;> simp [spinor2ToPeirce4, peirce4ToSpinor2]

@[simp] theorem spinor2ToPeirce4_peirce4ToSpinor2 (q : ℝ × V3) :
    spinor2ToPeirce4 (peirce4ToSpinor2 q) = q := by
  rcases q with ⟨a, v⟩
  apply Prod.ext
  · rfl
  · funext i
    fin_cases i <;> rfl

/-- Positive twistor sheet `(S₊)_ℝ ≃ ℝu₊ ⊕ V₊`. -/
noncomputable def twistorPlusEquivPeircePlus :
    TwistorPlus ≃ₗ[ℝ] PeircePlus4 where
  toLinearMap := spinor2ToPeirce4
  invFun := peirce4ToSpinor2
  left_inv := peirce4ToSpinor2_spinor2ToPeirce4
  right_inv := spinor2ToPeirce4_peirce4ToSpinor2

/-- Negative twistor sheet `(S₋)_ℝ ≃ ℝu₋ ⊕ V₋` in the repository's fixed
scalar-first circular Peirce order. -/
noncomputable def twistorMinusEquivPeirceMinus :
    TwistorMinus ≃ₗ[ℝ] PeirceMinus4 :=
  twistorPlusEquivPeircePlus

/-- Inclusion of the positive chiral sheet into the full twistor carrier. -/
def plusInclusion : TwistorPlus →ₗ[ℝ] Twistor4 where
  toFun ω := (ω, 0)
  map_add' ω ρ := by
    apply Prod.ext <;> simp
  map_smul' r ω := by
    apply Prod.ext <;> simp

/-- Inclusion of the negative chiral sheet into the full twistor carrier. -/
def minusInclusion : TwistorMinus →ₗ[ℝ] Twistor4 where
  toFun π := (0, π)
  map_add' π ρ := by
    apply Prod.ext <;> simp
  map_smul' r π := by
    apply Prod.ext <;> simp

@[simp] theorem plusInclusion_fst (ω : TwistorPlus) : (plusInclusion ω).1 = ω := rfl
@[simp] theorem plusInclusion_snd (ω : TwistorPlus) : (plusInclusion ω).2 = 0 := rfl
@[simp] theorem minusInclusion_fst (π : TwistorMinus) : (minusInclusion π).1 = 0 := rfl
@[simp] theorem minusInclusion_snd (π : TwistorMinus) : (minusInclusion π).2 = π := rfl

/-- The Penrose carrier is exactly the direct sum of its two chiral sheets. -/
theorem twistor_sheet_decomposition (Z : Twistor4) :
    plusInclusion Z.1 + minusInclusion Z.2 = Z := by
  apply Prod.ext <;> simp [plusInclusion, minusInclusion]

/-- Positive sheet embedded into the established Zorn carrier. -/
noncomputable def plusZornMap :
    TwistorPlus →ₗ[ℝ] CanonicalSplitOctonion :=
  twistorRealEquivZorn.toLinearMap.comp plusInclusion

/-- Negative sheet embedded into the established Zorn carrier. -/
noncomputable def minusZornMap :
    TwistorMinus →ₗ[ℝ] CanonicalSplitOctonion :=
  twistorRealEquivZorn.toLinearMap.comp minusInclusion

/-- The already established twistor-to-Zorn equivalence splits additively into
its positive and negative chiral-sheet images. -/
theorem twistor_zorn_sheet_decomposition (Z : Twistor4) :
    twistorRealEquivZorn Z = plusZornMap Z.1 + minusZornMap Z.2 := by
  rw [← twistor_sheet_decomposition Z, map_add]
  rfl

end InfoGeometry.Twistor.ChiralTwistorSheets
