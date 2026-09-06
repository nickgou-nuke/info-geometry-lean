import Mathlib

/-!
# Non-Hermitian Waveguide EP/Braid Specification

A finite theorem-level specification for the proposed physical realization of
Clifford/Artin braid gates in coupled non-Hermitian waveguides.

The model keeps the experimentally relevant invariant: for two balanced
waveguides with equal real propagation constants and gain/loss contrast `Δγ`,
the exceptional-point discriminant is

`κ² - (Δγ / 2)²`.

The EP condition is therefore `κ² = (Δγ / 2)²`, and in the physical quadrant
`κ ≥ 0`, `Δγ ≥ 0`, this is exactly `κ = Δγ / 2`.
-/

noncomputable section

namespace InfoGeometry.GrandUnification.WaveguideEPBraidSpec

/-- Real experimental parameters for one coupled two-waveguide gate. -/
structure WaveguidePairParams where
  betaMean : ℝ       -- common propagation constant offset
  gainLossContrast : ℝ -- `Δγ = γ₁ - γ₂`
  coupling : ℝ       -- evanescent coupling `κ`

/-- Balanced two-mode EP discriminant: `κ² - (Δγ/2)²`. -/
def epDiscriminant (P : WaveguidePairParams) : ℝ :=
  P.coupling ^ 2 - (P.gainLossContrast / 2) ^ 2

/-- The exceptional-point condition for the balanced two-waveguide gate. -/
def IsExceptionalPair (P : WaveguidePairParams) : Prop :=
  epDiscriminant P = 0

/-- In coordinates, the EP condition is exactly the vanishing discriminant equation. -/
theorem isExceptionalPair_iff (P : WaveguidePairParams) :
    IsExceptionalPair P ↔ P.coupling ^ 2 = (P.gainLossContrast / 2) ^ 2 := by
  unfold IsExceptionalPair epDiscriminant
  constructor <;> intro h
  · exact sub_eq_zero.mp h
  · exact sub_eq_zero.mpr h

/-- In the physical nonnegative quadrant, the EP condition is `κ = Δγ/2`. -/
theorem isExceptionalPair_iff_nonneg
    (P : WaveguidePairParams)
    (hκ : 0 ≤ P.coupling) (hγ : 0 ≤ P.gainLossContrast) :
    IsExceptionalPair P ↔ P.coupling = P.gainLossContrast / 2 := by
  rw [isExceptionalPair_iff]
  constructor
  · intro hsq
    have hhalf : 0 ≤ P.gainLossContrast / 2 := by positivity
    exact sq_eq_sq_iff_eq_or_eq_neg.mp hsq |>.elim id (fun hneg => by
      have hhalf_nonpos : P.gainLossContrast / 2 ≤ 0 := by
        exact neg_nonneg.mp (hneg ▸ hκ)
      have hhalf_zero : P.gainLossContrast / 2 = 0 := le_antisymm hhalf_nonpos hhalf
      rw [hneg, hhalf_zero, neg_zero])
  · intro h
    rw [h]

/-- A finite braid protocol for three waveguides: left sequence `12,23,12`. -/
def leftArtinProtocol : List (Fin 2) := [0, 1, 0]

/-- Right sequence `23,12,23`. -/
def rightArtinProtocol : List (Fin 2) := [1, 0, 1]

/-- Both experimental Artin protocols have the same length. -/
theorem artin_protocol_lengths_equal :
    leftArtinProtocol.length = rightArtinProtocol.length := by
  rfl

/-- A length-only loss/gain budget for a braid protocol. -/
def protocolGainBudget (singleGateGain : ℝ) (w : List (Fin 2)) : ℝ :=
  singleGateGain ^ w.length

/-- The two adjacent Artin protocols have identical length-only gain budget. -/
theorem artin_protocol_gain_budget_equal (g : ℝ) :
    protocolGainBudget g leftArtinProtocol = protocolGainBudget g rightArtinProtocol := by
  simp [protocolGainBudget, artin_protocol_lengths_equal]

end InfoGeometry.GrandUnification.WaveguideEPBraidSpec
