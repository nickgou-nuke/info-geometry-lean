import InfoGeometry.Canonical.BipolarTwoSheetCore
import InfoGeometry.Algebra.RealPauliCausalCone
import Mathlib.Tactic

/-!
# Two-sheet boundary to causal-bulk bridge

The two-sheet carrier supplies a canonical finite realification mechanism.
A complex boundary phase has two real components; together with the two-sheet
involution one obtains even/odd real coordinates.  Independently, the repository
already owns the four-real-coordinate causal carrier `RealPauliOp`.

This file records only exact finite algebra:

* a two-sheet complex amplitude determines four real coordinates;
* pure sheet exchange fixes the even coordinates and negates the odd ones;
* a unit-modulus critical phase determines the null Minkowski vector
  `(1, Re u, Im u, 0)`;
* the critical Cayley phase therefore lands exactly on the native causal cone
  `detMinkowski = 0`;
* deck-related boundary lifts have the same projected null bulk point when the
  bulk projection depends only on the underlying unit-circle phase.

No AdS/CFT theorem, continuum holographic reconstruction, Einstein equation,
or causal-completion theorem is asserted.
-/

noncomputable section

namespace InfoGeometry.Canonical.BipolarTwoSheetCausalBulkBridge

open InfoGeometry.Canonical.BipolarTwoSheetCore
open InfoGeometry.Analysis.BipolarCrossRatioLog
open InfoGeometry.Analysis.BipolarCriticalPhase
open InfoGeometry.Topology.Weyl
open InfoGeometry.Algebra.RealPauliCausalCone

/-- Four real coordinates obtained from the even/odd decomposition of a
complex two-sheet amplitude. -/
def realifySheetAmplitude (ψ : SheetAmplitude) : RealPauliOp :=
  ⟨(sheetEven ψ).re,
   (sheetOdd ψ).re,
   (sheetEven ψ).im,
   (sheetOdd ψ).im⟩

/-- Readout of the four real coordinates. -/
@[simp] theorem realifySheetAmplitude_t (ψ : SheetAmplitude) :
    (realifySheetAmplitude ψ).t = (sheetEven ψ).re := rfl

@[simp] theorem realifySheetAmplitude_x (ψ : SheetAmplitude) :
    (realifySheetAmplitude ψ).x = (sheetOdd ψ).re := rfl

@[simp] theorem realifySheetAmplitude_y (ψ : SheetAmplitude) :
    (realifySheetAmplitude ψ).y = (sheetEven ψ).im := rfl

@[simp] theorem realifySheetAmplitude_z (ψ : SheetAmplitude) :
    (realifySheetAmplitude ψ).z = (sheetOdd ψ).im := rfl

/-- Deck exchange acts diagonally on the four realified coordinates: the even
coordinates are fixed and the odd coordinates change sign. -/
theorem realify_swapAmplitude (ψ : SheetAmplitude) :
    realifySheetAmplitude (swapAmplitude ψ) =
      ⟨(realifySheetAmplitude ψ).t,
       -(realifySheetAmplitude ψ).x,
       (realifySheetAmplitude ψ).y,
       -(realifySheetAmplitude ψ).z⟩ := by
  apply Prod.ext
  · simp [realifySheetAmplitude]
  · apply Prod.ext
    · simp [realifySheetAmplitude]
    · apply Prod.ext <;> simp [realifySheetAmplitude]

/-- Native causal-bulk lift of one unit-circle boundary phase.
The final coordinate is set to zero, selecting a canonical 2+1-dimensional
null section inside the four-real-coordinate carrier. -/
def nullBulkOfPhase (u : ℂ) : RealPauliOp :=
  ⟨1, u.re, u.im, 0⟩

@[simp] theorem nullBulkOfPhase_t (u : ℂ) : (nullBulkOfPhase u).t = 1 := rfl
@[simp] theorem nullBulkOfPhase_x (u : ℂ) : (nullBulkOfPhase u).x = u.re := rfl
@[simp] theorem nullBulkOfPhase_y (u : ℂ) : (nullBulkOfPhase u).y = u.im := rfl
@[simp] theorem nullBulkOfPhase_z (u : ℂ) : (nullBulkOfPhase u).z = 0 := rfl

/-- Unit-modulus phases land exactly on the native Minkowski null cone. -/
theorem nullBulkOfPhase_lightlike {u : ℂ} (hu : ‖u‖ = 1) :
    detMinkowski (nullBulkOfPhase u) = 0 := by
  have hnormSq : Complex.normSq u = 1 := by
    rw [Complex.normSq_eq_norm_sq, hu]
    norm_num
  rw [Complex.normSq_apply] at hnormSq
  simp [detMinkowski, nullBulkOfPhase, RealPauliOp.t,
    RealPauliOp.x, RealPauliOp.y, RealPauliOp.z]
  nlinarith

/-- Scaling a null bulk representative preserves nullness. -/
theorem nullBulkOfPhase_smul_lightlike {u : ℂ} (hu : ‖u‖ = 1) (c : ℝ) :
    detMinkowski (smul c (nullBulkOfPhase u)) = 0 := by
  have hnull := nullBulkOfPhase_lightlike hu
  simp [detMinkowski, smul, RealPauliOp.t, RealPauliOp.x,
    RealPauliOp.y, RealPauliOp.z] at hnull ⊢
  nlinarith

/-- Critical-line Cayley phase lifted to the causal bulk. -/
def criticalNullBulk (y : ℝ) : RealPauliOp :=
  nullBulkOfPhase (criticalPhase y)

/-- Every critical-line phase gives a native null bulk representative. -/
theorem criticalNullBulk_lightlike (y : ℝ) :
    detMinkowski (criticalNullBulk y) = 0 := by
  exact nullBulkOfPhase_lightlike (norm_criticalPhase y)

/-- The critical-line Cayley coordinate and the rational phase produce exactly
the same null bulk representative. -/
theorem criticalNullBulk_eq_crossRatio (y : ℝ) :
    criticalNullBulk y = nullBulkOfPhase (crossRatio01 (criticalLine y)) := by
  rw [criticalNullBulk, crossRatio01_criticalLine_eq_criticalPhase]

/-- Conjugating a boundary phase reflects the transverse imaginary coordinate
of its null bulk lift while preserving the other three coordinates. -/
theorem nullBulkOfPhase_conj (u : ℂ) :
    nullBulkOfPhase (Complex.conj u) =
      ⟨(nullBulkOfPhase u).t,
       (nullBulkOfPhase u).x,
       -(nullBulkOfPhase u).y,
       (nullBulkOfPhase u).z⟩ := by
  apply Prod.ext
  · simp [nullBulkOfPhase]
  · apply Prod.ext
    · simp [nullBulkOfPhase]
    · apply Prod.ext <;> simp [nullBulkOfPhase]

/-- The two critical sheet phases determine conjugate null representatives.
Thus the sheet exchange is visible in the bulk as reversal of one transverse
coordinate, while both representatives remain on the same null cone. -/
theorem critical_two_sheet_null_pair (y : ℝ) :
    detMinkowski (nullBulkOfPhase (criticalSheetPhase y ChiralSheet.plus)) = 0 ∧
    detMinkowski (nullBulkOfPhase (criticalSheetPhase y ChiralSheet.minus)) = 0 ∧
    nullBulkOfPhase (criticalSheetPhase y ChiralSheet.minus) =
      ⟨(nullBulkOfPhase (criticalSheetPhase y ChiralSheet.plus)).t,
       (nullBulkOfPhase (criticalSheetPhase y ChiralSheet.plus)).x,
       -(nullBulkOfPhase (criticalSheetPhase y ChiralSheet.plus)).y,
       (nullBulkOfPhase (criticalSheetPhase y ChiralSheet.plus)).z⟩ := by
  constructor
  · simpa [criticalSheetPhase] using criticalNullBulk_lightlike y
  constructor
  · have hnorm : ‖Complex.conj (criticalPhase y)‖ = 1 := by
      simpa using norm_criticalPhase y
    simpa [criticalSheetPhase] using nullBulkOfPhase_lightlike hnorm
  · simpa [criticalSheetPhase] using nullBulkOfPhase_conj (criticalPhase y)

/-- Compact boundary-to-bulk packet: the two-sheet critical pair is represented
by two conjugate null points in the repository-owned four-real-coordinate
causal carrier. -/
theorem two_sheet_causal_bulk_packet (y : ℝ) :
    sheetMirror (plusLift (criticalLine y)) = minusLift (criticalLine y) ∧
    detMinkowski (criticalNullBulk y) = 0 ∧
    detMinkowski (nullBulkOfPhase (criticalSheetPhase y ChiralSheet.minus)) = 0 := by
  exact ⟨sheetMirror_plus_criticalLine y,
    criticalNullBulk_lightlike y,
    (critical_two_sheet_null_pair y).2.1⟩

end InfoGeometry.Canonical.BipolarTwoSheetCausalBulkBridge
