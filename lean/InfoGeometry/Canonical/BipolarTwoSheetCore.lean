import InfoGeometry.Analysis.BipolarCrossRatioLog
import InfoGeometry.Analysis.BipolarApolloniusReflectionMetric
import InfoGeometry.Analysis.BipolarCriticalPhase
import InfoGeometry.Topology.TwistedCohomologyWeyl
import InfoGeometry.OperatorAlgebra.AndreevBoundary
import Mathlib.Tactic

/-!
# Two-sheet core for the bipolar construction

The common algebraic carrier behind the informal incoming/outgoing,
particle/hole, and mirror-paired language is a two-sheet cover.

This file reuses the repository-owned `ChiralSheet` and its deck involution
`swap`.  The base is the bipolar `s`-plane.  The lifted mirror simultaneously
swaps sheets and applies `s ↦ 1-conj(s)` to the base.

On the critical line the base point is fixed, but the two lifts are exchanged.
Thus the interface is a fixed locus only after projection to the base.

No physical identification of the two sheets is primitive.  Electron/hole,
incoming/outgoing, or other interpretations are adapters.
-/

noncomputable section

namespace InfoGeometry.Canonical.BipolarTwoSheetCore

open InfoGeometry.Analysis.BipolarCrossRatioLog
open InfoGeometry.Analysis.BipolarApolloniusReflectionMetric
open InfoGeometry.Analysis.BipolarCriticalPhase
open InfoGeometry.Topology.Weyl
open InfoGeometry.OperatorAlgebra.AndreevBoundary

/-- Two-sheet lift of a base type. -/
abbrev TwoSheet (X : Type*) := ChiralSheet × X

/-- Projection to the base. -/
def baseProjection {X : Type*} (x : TwoSheet X) : X := x.2

/-- Pure deck transformation: exchange sheets and leave the base fixed. -/
def deck {X : Type*} : TwoSheet X → TwoSheet X :=
  fun x => (x.1.swap, x.2)

@[simp] theorem deck_involutive {X : Type*} (x : TwoSheet X) :
    deck (deck x) = x := by
  rcases x with ⟨sh, x⟩
  cases sh <;> rfl

@[simp] theorem baseProjection_deck {X : Type*} (x : TwoSheet X) :
    baseProjection (deck x) = baseProjection x := rfl

/-- Lifted bipolar mirror: exchange the sheet and reflect the base. -/
def sheetMirror : TwoSheet ℂ → TwoSheet ℂ :=
  fun x => (x.1.swap, mirror x.2)

private theorem mirror_criticalLine (y : ℝ) :
    mirror (criticalLine y) = criticalLine y := by
  unfold mirror criticalLine
  simp only [map_add, map_ofNat, map_mul, Complex.star_def, Complex.conj_ofReal,
    Complex.conj_I]
  norm_num
  ring

@[simp] theorem sheetMirror_involutive (x : TwoSheet ℂ) :
    sheetMirror (sheetMirror x) = x := by
  rcases x with ⟨sh, s⟩
  cases sh <;> simp [sheetMirror, mirror_involutive]

@[simp] theorem baseProjection_sheetMirror (x : TwoSheet ℂ) :
    baseProjection (sheetMirror x) = mirror (baseProjection x) := rfl

/-- The two canonical lifts of one base point. -/
def plusLift (s : ℂ) : TwoSheet ℂ := (ChiralSheet.plus, s)

def minusLift (s : ℂ) : TwoSheet ℂ := (ChiralSheet.minus, s)

@[simp] theorem deck_plusLift (s : ℂ) : deck (plusLift s) = minusLift s := rfl
@[simp] theorem deck_minusLift (s : ℂ) : deck (minusLift s) = plusLift s := rfl

/-- On the critical line, the lifted mirror exchanges the two sheets over the
same base point. -/
theorem sheetMirror_plus_criticalLine (y : ℝ) :
    sheetMirror (plusLift (criticalLine y)) = minusLift (criticalLine y) := by
  simp [sheetMirror, plusLift, minusLift, mirror_criticalLine]

/-- The reverse critical-line exchange. -/
theorem sheetMirror_minus_criticalLine (y : ℝ) :
    sheetMirror (minusLift (criticalLine y)) = plusLift (criticalLine y) := by
  simp [sheetMirror, plusLift, minusLift, mirror_criticalLine]

/-- The critical-line point is fixed downstairs while its two lifts are swapped
upstairs. -/
theorem criticalLine_fixed_downstairs_swapped_upstairs (y : ℝ) :
    baseProjection (sheetMirror (plusLift (criticalLine y))) = criticalLine y ∧
      sheetMirror (plusLift (criticalLine y)) = minusLift (criticalLine y) := by
  constructor
  · change mirror (criticalLine y) = criticalLine y
    exact mirror_criticalLine y
  · exact sheetMirror_plus_criticalLine y

/-- Sheet-dependent multiplicative readout: the minus sheet carries the complex
conjugate of the plus-sheet Cayley mode. -/
def sheetCayleyReadout : TwoSheet ℂ → ℂ
  | (ChiralSheet.plus, s) => crossRatio01 s
  | (ChiralSheet.minus, s) => (starRingEnd ℂ) (crossRatio01 s)

/-- Lifted mirror sends either sheet readout to its multiplicative inverse. -/
theorem sheetCayleyReadout_sheetMirror
    {x : TwoSheet ℂ} (hx : baseProjection x ∈ punctured01) :
    sheetCayleyReadout (sheetMirror x) = (sheetCayleyReadout x)⁻¹ := by
  rcases x with ⟨sh, s⟩
  cases sh
  · simp [sheetCayleyReadout, sheetMirror, baseProjection, crossRatio01_mirror]
  · simp [sheetCayleyReadout, sheetMirror, baseProjection, crossRatio01_mirror]

/-- On the critical line, the two sheet readouts are mutual inverses. -/
theorem criticalLine_sheet_readouts_inverse (y : ℝ) :
    sheetCayleyReadout (minusLift (criticalLine y)) =
      (sheetCayleyReadout (plusLift (criticalLine y)))⁻¹ := by
  rw [← sheetMirror_plus_criticalLine y]
  exact sheetCayleyReadout_sheetMirror
    (x := plusLift (criticalLine y)) (criticalLine_mem_punctured01 y)

/-- Adapter from the sheet label to the repository-owned Andreev channel label. -/
def sheetToAndreevChannel : ChiralSheet → AndreevChannel
  | ChiralSheet.plus => AndreevChannel.electronLike
  | ChiralSheet.minus => AndreevChannel.holeLike

/-- Sheet swap intertwines the Andreev channel flip. -/
theorem sheetToAndreevChannel_swap (sh : ChiralSheet) :
    sheetToAndreevChannel sh.swap = AndreevChannel.flip (sheetToAndreevChannel sh) := by
  cases sh <;> rfl

/-- A two-sheet complex amplitude. -/
abbrev SheetAmplitude := ChiralSheet → ℂ

/-- Anti-linear deck closure: sheet exchange plus complex conjugation. -/
def antiLinearDeck (ψ : SheetAmplitude) : SheetAmplitude :=
  fun sh => (starRingEnd ℂ) (ψ sh.swap)

@[simp] theorem antiLinearDeck_sq (ψ : SheetAmplitude) :
    antiLinearDeck (antiLinearDeck ψ) = ψ := by
  funext sh
  cases sh <;> simp [antiLinearDeck]

/-- Critical-line phase placed on the two sheets as conjugate partners. -/
def criticalSheetPhase (y : ℝ) : SheetAmplitude
  | ChiralSheet.plus => criticalPhase y
  | ChiralSheet.minus => (starRingEnd ℂ) (criticalPhase y)

/-- The critical two-sheet phase is fixed by the anti-linear deck closure. -/
theorem criticalSheetPhase_fixed (y : ℝ) :
    antiLinearDeck (criticalSheetPhase y) = criticalSheetPhase y := by
  funext sh
  cases sh <;> simp [antiLinearDeck, criticalSheetPhase]

/-- Even component of a two-sheet complex amplitude. -/
def sheetEven (ψ : SheetAmplitude) : ℂ :=
  (ψ ChiralSheet.plus + ψ ChiralSheet.minus) / 2

/-- Odd component of a two-sheet complex amplitude. -/
def sheetOdd (ψ : SheetAmplitude) : ℂ :=
  (ψ ChiralSheet.plus - ψ ChiralSheet.minus) / 2

/-- Reconstruction of the plus sheet from even and odd components. -/
theorem plus_eq_even_add_odd (ψ : SheetAmplitude) :
    ψ ChiralSheet.plus = sheetEven ψ + sheetOdd ψ := by
  simp [sheetEven, sheetOdd]
  ring

/-- Reconstruction of the minus sheet from even and odd components. -/
theorem minus_eq_even_sub_odd (ψ : SheetAmplitude) :
    ψ ChiralSheet.minus = sheetEven ψ - sheetOdd ψ := by
  simp [sheetEven, sheetOdd]
  ring

/-- Pure sheet exchange preserves the even component. -/
def swapAmplitude (ψ : SheetAmplitude) : SheetAmplitude := fun sh => ψ sh.swap

@[simp] theorem sheetEven_swapAmplitude (ψ : SheetAmplitude) :
    sheetEven (swapAmplitude ψ) = sheetEven ψ := by
  simp [sheetEven, swapAmplitude]
  ring

/-- Pure sheet exchange negates the odd component. -/
@[simp] theorem sheetOdd_swapAmplitude (ψ : SheetAmplitude) :
    sheetOdd (swapAmplitude ψ) = -sheetOdd ψ := by
  simp [sheetOdd, swapAmplitude]
  ring

/-- Compact two-sheet packet. -/
theorem two_sheet_core_packet (y : ℝ) :
    sheetMirror (plusLift (criticalLine y)) = minusLift (criticalLine y) ∧
      sheetCayleyReadout (minusLift (criticalLine y)) =
        (sheetCayleyReadout (plusLift (criticalLine y)))⁻¹ ∧
      antiLinearDeck (criticalSheetPhase y) = criticalSheetPhase y := by
  exact ⟨sheetMirror_plus_criticalLine y,
    criticalLine_sheet_readouts_inverse y,
    criticalSheetPhase_fixed y⟩

end InfoGeometry.Canonical.BipolarTwoSheetCore
