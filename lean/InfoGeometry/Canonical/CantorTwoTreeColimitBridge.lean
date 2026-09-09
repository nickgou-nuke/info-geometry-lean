import Mathlib.Analysis.Complex.Basic
import Mathlib.Tactic
import InfoGeometry.Canonical.FractalCantorCliffordFockBridge
import InfoGeometry.Canonical.CantorBoundaryComplexReadout
import InfoGeometry.Canonical.CantorBoundaryTomitaBridge
import InfoGeometry.Canonical.ColimitRigidityFixedLocusBridge

/-!
# Cantor two-tree colimit bridge

This file connects the exploratory `ℕ → Fin 2` carrier used in this module to the
repository’s existing Cantor boundary readout `CantorBoundary := ℕ → Bool` and
uses the repository-verified Tomita/complement + fixed-state lemmas to prove the
critical-line projection without extra assumptions.
-/

noncomputable section

namespace CantorTwoTree

open Complex
open InfoGeometry.Canonical.FractalCantorCliffordFockBridge
open InfoGeometry.Canonical.CantorBoundaryComplexReadout
open InfoGeometry.Canonical.CantorBoundaryTomitaBridge
open InfoGeometry.Canonical.ColimitRigidityFixedLocusBridge

/-- `Fin 2`-valued infinite binary word used for the colimit construction. -/
def InfiniteBinaryWord := ℕ → Fin 2

def tomitaWordConjugation (w : InfiniteBinaryWord) : InfiniteBinaryWord :=
  fun n => 1 - w n

theorem tomita_word_conjugation_involutive (w : InfiniteBinaryWord) :
    tomitaWordConjugation (tomitaWordConjugation w) = w := by
  funext n
  cases h : w n with
  | mk val isLt =>
    have h01 : val = 0 ∨ val = 1 := by omega
    rcases h01 with h0 | h1
    · simp [tomitaWordConjugation, h, h0]
    · simp [tomitaWordConjugation, h, h1]

/-- Convert `Fin 2` digits to repository boundary booleans (`false ↔ 0`, `true ↔ 1`). -/
def fromFin2 (w : InfiniteBinaryWord) : InfiniteBinaryWordSpace :=
  fun n => w n = 1

/-- Readout on `Fin 2` words as an absolutely convergent geometric `tsum`. -/
noncomputable def wordToComplex (w : InfiniteBinaryWord) : ℂ :=
  ∑' n : ℕ, w n / (2 ^ (n + 1) : ℂ)

/-- `wordToComplex` agrees with the repository `binaryReadout` after `fromFin2`. -/
lemma wordToComplex_eq_binaryReadout (w : InfiniteBinaryWord) :
    wordToComplex w = binaryReadout (fromFin2 w) := by
  unfold wordToComplex binaryReadout binaryTerm
  refine tsum_congr ?_
  intro n
  cases h : w n with
  | mk val isLt =>
    have h01 : val = 0 ∨ val = 1 := by omega
    rcases h01 with h0 | h1
    · simp [h, fromFin2, binaryDigit, h0]
    · simp [h, fromFin2, binaryDigit, h1]

/-- Tomita conjugation is Boolean complement after `fromFin2`. -/
lemma fromFin2_tomita (w : InfiniteBinaryWord) (n : ℕ) :
    fromFin2 (tomitaWordConjugation w) n = !(fromFin2 w n) := by
  cases h : w n with
  | mk val isLt =>
    have h01 : val = 0 ∨ val = 1 := by omega
    rcases h01 with h0 | h1
    · simp [tomitaWordConjugation, fromFin2, h, h0]
    · simp [tomitaWordConjugation, fromFin2, h, h1]

/--
A state fixed under the Tomita-twisted readout has real part `1/2` on the
critical line.
-/
theorem cantor_colimit_state_on_critical_line
    (w : InfiniteBinaryWord)
    (z : ℂ)
    (h_eval : z = wordToComplex w)
    (h_invariant : wordToComplex (tomitaWordConjugation w) = star (wordToComplex w)) :
    z.re = 1 / 2 := by
  have h_tomita_bool :
      InfoGeometry.Canonical.CantorTwoTreeFixedLocus.tomitaWordConjugation (fromFin2 w) =
        fromFin2 (tomitaWordConjugation w) := by
    ext n
    simpa [InfoGeometry.Canonical.CantorTwoTreeFixedLocus.tomitaWordConjugation] using
      (fromFin2_tomita w n).symm

  have h_bool_invariant' :
      binaryReadout (fromFin2 (tomitaWordConjugation w)) = star (binaryReadout (fromFin2 w)) := by
    simpa [wordToComplex_eq_binaryReadout] using h_invariant
  have h_bool_invariant :
      binaryReadout (InfoGeometry.Canonical.CantorTwoTreeFixedLocus.tomitaWordConjugation (fromFin2 w)) =
        star (binaryReadout (fromFin2 w)) := by
    simpa [h_tomita_bool] using h_bool_invariant'
  have h_bool_state :
      (binaryReadout (fromFin2 w)).re = 1 / 2 :=
    binary_readout_tomita_fixed_state_on_critical_line
      (fromFin2 w)
      h_bool_invariant
  have h_eval' : z = binaryReadout (fromFin2 w) := by
    simpa [wordToComplex_eq_binaryReadout] using h_eval
  simpa [h_eval'] using h_bool_state

end CantorTwoTree
