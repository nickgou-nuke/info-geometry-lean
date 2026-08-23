import InfoGeometry.Twistor.RealSplitOctonionCarrierBridge
import Mathlib.Tactic.FinCases

/-!
# Chiral twistor Peirce sheets

The Penrose twistor carrier is already `Twistor4 = Spinor2 × Spinor2`, with
`Spinor2 = Fin 2 → ℂ`.  This owner does not introduce a second twistor
carrier API.  It aliases the two existing spinor factors and identifies each,
as a real four-dimensional vector space, with one of the two four-dimensional
Peirce halves of the established circular Zorn ordering.

The repository convention is

`u₊ | V₊ | u₋ | V₋`,

so both Peirce halves are stored as `ℝ × ℝ³`: scalar first, then the three
root coordinates.  Abstractly the negative half may equally be written
`V₋ ⊕ ℝ u₋`; changing to that order requires an explicit permutation
linear equivalence and is not done silently here.

No multiplication is defined in this file.  The Zorn coupling is owned by the
native split-octonion multiplication table and is connected in a separate
module.
-/

noncomputable section

namespace InfoGeometry.Twistor.ChiralTwistorPeirceSheets

open InfoGeometry.Twistor.PenroseIncidence
open InfoGeometry.Twistor.RealSplitOctonionCarrierBridge
open InfoGeometry.Canonical.SplitOctonionExterior3HodgeDiracBridge

/-- Existing positive Penrose spinor factor. -/
abbrev TwistorPlus := Spinor2

/-- Existing negative Penrose spinor factor. -/
abbrev TwistorMinus := Spinor2

/-- Positive Peirce half `ℝu₊ ⊕ V₊` in scalar-first repository order. -/
abbrev PeircePlus4 := ℝ × V3

/-- Negative Peirce half `ℝu₋ ⊕ V₋` in scalar-first repository order. -/
abbrev PeirceMinus4 := ℝ × V3

/-- Real coordinates on either two-component complex spinor, ordered as
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

/-- Reconstruct a chiral complex spinor from four real Peirce coordinates. -/
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
  fin_cases i <;> apply Complex.ext <;>
    simp [spinor2ToPeirce4, peirce4ToSpinor2]

@[simp] theorem spinor2ToPeirce4_peirce4ToSpinor2 (q : ℝ × V3) :
    spinor2ToPeirce4 (peirce4ToSpinor2 q) = q := by
  rcases q with ⟨a, v⟩
  apply Prod.ext
  · rfl
  · funext i
    fin_cases i <;> rfl

/-- Positive Penrose sheet `(S₊)_ℝ ≃ ℝu₊ ⊕ V₊`. -/
noncomputable def twistorPlusEquivPeircePlus :
    TwistorPlus ≃ₗ[ℝ] PeircePlus4 where
  toLinearMap := spinor2ToPeirce4
  invFun := peirce4ToSpinor2
  left_inv := peirce4ToSpinor2_spinor2ToPeirce4
  right_inv := spinor2ToPeirce4_peirce4ToSpinor2

/-- Negative Penrose sheet `(S₋)_ℝ ≃ ℝu₋ ⊕ V₋` in the established
scalar-first circular Peirce order. -/
noncomputable def twistorMinusEquivPeirceMinus :
    TwistorMinus ≃ₗ[ℝ] PeirceMinus4 :=
  twistorPlusEquivPeircePlus

/-- Inclusion of the existing positive spinor factor into `Twistor4`. -/
def plusInclusion : Spinor2 →ₗ[ℝ] Twistor4 where
  toFun ω := (ω, 0)
  map_add' ω ρ := by
    apply Prod.ext
    · rfl
    · simp
  map_smul' r ω := by
    apply Prod.ext
    · rfl
    · simp

/-- Inclusion of the existing negative spinor factor into `Twistor4`. -/
def minusInclusion : Spinor2 →ₗ[ℝ] Twistor4 where
  toFun π := (0, π)
  map_add' π ρ := by
    apply Prod.ext
    · simp
    · rfl
  map_smul' r π := by
    apply Prod.ext
    · simp
    · rfl

@[simp] theorem plusInclusion_fst (ω : Spinor2) : (plusInclusion ω).1 = ω := rfl
@[simp] theorem plusInclusion_snd (ω : Spinor2) : (plusInclusion ω).2 = 0 := rfl
@[simp] theorem minusInclusion_fst (π : Spinor2) : (minusInclusion π).1 = 0 := rfl
@[simp] theorem minusInclusion_snd (π : Spinor2) : (minusInclusion π).2 = π := rfl

/-- The existing Penrose carrier is exactly the sum of its two spinor sheets. -/
theorem twistor_sheet_decomposition (Z : Twistor4) :
    plusInclusion Z.1 + minusInclusion Z.2 = Z := by
  apply Prod.ext <;> simp [plusInclusion, minusInclusion]

/-- Positive sheet followed by the established twistor-to-Zorn map. -/
noncomputable def plusZornMap :
    Spinor2 →ₗ[ℝ] CanonicalSplitOctonion :=
  twistorRealEquivZorn.toLinearMap.comp plusInclusion

/-- Negative sheet followed by the established twistor-to-Zorn map. -/
noncomputable def minusZornMap :
    Spinor2 →ₗ[ℝ] CanonicalSplitOctonion :=
  twistorRealEquivZorn.toLinearMap.comp minusInclusion

/-- Sheetwise factorization of the already existing
`twistorRealEquivZorn : Twistor4 ≃ₗ[ℝ] CanonicalSplitOctonion`. -/
theorem twistor_zorn_sheet_decomposition (Z : Twistor4) :
    twistorRealEquivZorn Z = plusZornMap Z.1 + minusZornMap Z.2 := by
  rw [← twistor_sheet_decomposition Z, map_add]
  rfl

end InfoGeometry.Twistor.ChiralTwistorPeirceSheets
