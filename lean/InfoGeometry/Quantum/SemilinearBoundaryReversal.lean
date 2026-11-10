/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.Quantum.BoundaryInstrument
import InfoGeometry.Quantum.MixedBoundaryReadout
import InfoGeometry.OperatorAlgebra.SemilinearSheetGeometry

/-!
# Semilinear reversal of two-boundary matrix instruments

The existing real algebra involution exchanges the two full matrix sectors
and conjugates coefficients. Instrument reversal also swaps the boundary
operators and adjoints the Kraus family. This algebraic reversal is distinct
from assuming that the reversed family is a trace-preserving channel.
-/

noncomputable section

namespace InfoGeometry.Quantum.SemilinearBoundaryReversal

open Matrix
open InfoGeometry.OperatorAlgebra.SemilinearSheetGeometry
open InfoGeometry.Quantum.BoundaryInstrument
open InfoGeometry.Quantum.MixedBoundaryReadout
open scoped BigOperators

variable {n : Type*} [Fintype n] [DecidableEq n]
variable {k : Type*} [Fintype k] [DecidableEq k]

/-- Semilinear conjugation transports the existing Kraus map without reversing products. -/
theorem sheetConj_krausMap (V : k → SheetMatrix n) (X : SheetMatrix n) :
    Choi.krausMap (fun i => sheetConj (V i)) (sheetConj X) =
      sheetConj (Choi.krausMap V X) := by
  simp only [Choi.krausMap, LinearMap.coe_mk, AddHom.coe_mk, map_sum,
    map_mul, sheetConj_star]

/-- Conjugation commutes with chronological words on the full operator algebra. -/
theorem sheetConj_forwardWord (word : List (k → SheetMatrix n)) (X : SheetMatrix n) :
    Choi.forwardWord (word.map (fun V i => sheetConj (V i))) (sheetConj X) =
      sheetConj (Choi.forwardWord word X) := by
  induction word generalizing X with
  | nil => rfl
  | cons V tail ih =>
      simp only [List.map_cons, Choi.forwardWord_cons, LinearMap.comp_apply]
      rw [sheetConj_krausMap, ih]

/-- The reversed elementary operation includes the adjoint, not only coefficient conjugation. -/
def reversedKraus (V : k → SheetMatrix n) (i : k) : SheetMatrix n :=
  sheetConj (star (V i))

omit [Fintype k] [DecidableEq k] in
@[simp] theorem reversedKraus_twice (V : k → SheetMatrix n) :
    reversedKraus (reversedKraus V) = V := by
  funext i
  simp only [reversedKraus, ← sheetConj_star, star_star, sheetConj_involutive]

/-- Real boundary weight is invariant under boundary exchange and adjoint reversal. -/
theorem reversed_trace_weight (V : k → SheetMatrix n) (ρ E : SheetMatrix n) :
    (trace (Choi.krausMap (reversedKraus V) (sheetConj E) * sheetConj ρ)).re =
      (trace (Choi.krausMap V ρ * E)).re := by
  unfold reversedKraus
  rw [sheetConj_krausMap, ← map_mul, trace_sheetConj]
  rw [Choi.trace_krausMap_pairing]
  simp only [star_star]
  rw [trace_mul_comm E (Choi.krausMap V ρ)]
  rfl

/-- Reversing an adjointed chronological word gives the existing backward action. -/
theorem forwardWord_reverse_adjoint (word : List (k → SheetMatrix n)) :
    Choi.forwardWord (word.reverse.map (fun V i => star (V i))) =
      Choi.backwardWord word := by
  induction word with
  | nil => rfl
  | cons V tail ih =>
      simp only [List.reverse_cons, List.map_append, List.map_cons, List.map_nil,
        Choi.forwardWord_append, ih]
      ext X
      rfl

/-- Entire chronological words reverse, including their Kraus order and endpoints. -/
theorem reversed_word_weight (word : List (k → SheetMatrix n)) (ρ E : SheetMatrix n) :
    (trace (Choi.forwardWord (word.reverse.map reversedKraus) (sheetConj E) *
      sheetConj ρ)).re = (trace (Choi.forwardWord word ρ * E)).re := by
  have hmap : word.reverse.map reversedKraus =
      (word.reverse.map (fun V i => star (V i))).map (fun V i => sheetConj (V i)) := by
    simp only [List.map_map]
    rfl
  rw [hmap, sheetConj_forwardWord, forwardWord_reverse_adjoint, ← map_mul, trace_sheetConj,
    trace_mul_comm (Choi.backwardWord word E) ρ, ← Choi.trace_forwardWord_pairing]
  rfl

variable {o : Type*} [Fintype o] [DecidableEq o]

omit [Fintype o] [DecidableEq o] in
theorem outcomeWeight_reversed (V : o → k → SheetMatrix n) (ρ E : SheetMatrix n) (a : o) :
    outcomeWeight (fun a => reversedKraus (V a)) (sheetConj E) (sheetConj ρ) a =
      outcomeWeight V ρ E a :=
  reversed_trace_weight (V a) ρ E

omit [DecidableEq o] in
theorem normalizer_reversed (V : o → k → SheetMatrix n) (ρ E : SheetMatrix n) :
    normalizer (fun a => reversedKraus (V a)) (sheetConj E) (sheetConj ρ) =
      normalizer V ρ E := by
  simp only [normalizer, outcomeWeight_reversed]

omit [DecidableEq o] in
theorem probability_reversed (V : o → k → SheetMatrix n) (ρ E : SheetMatrix n) (a : o) :
    probability (fun a => reversedKraus (V a)) (sheetConj E) (sheetConj ρ) a =
      probability V ρ E a := by
  simp only [probability, outcomeWeight_reversed, normalizer_reversed]

omit [DecidableEq k] in
/-- Reversed completeness is the conjugate of original unitality. -/
theorem reversed_completeness (V : k → SheetMatrix n) :
    (∑ i, star (reversedKraus V i) * reversedKraus V i) =
      sheetConj (∑ i, V i * star (V i)) := by
  simp only [reversedKraus, ← sheetConj_star, star_star, map_sum, map_mul]

/-- Reversed trace preservation holds exactly when the original map is unital. -/
theorem reversed_trace_preserving_iff (V : k → SheetMatrix n) :
    (∀ X, trace (Choi.krausMap (reversedKraus V) X) = trace X) ↔
      Choi.krausMap V (1 : SheetMatrix n) = 1 := by
  rw [Choi.krausMap_trace_preserving_iff]
  have h : Choi.krausMap (fun i => star (reversedKraus V i)) (1 : SheetMatrix n) =
      sheetConj (Choi.krausMap V 1) := by
    simp only [Choi.krausMap, LinearMap.coe_mk, AddHom.coe_mk, mul_one,
      reversedKraus, ← sheetConj_star, star_star, map_sum, map_mul]
  rw [h]
  constructor
  · intro heq
    apply (sheetConj (n := n)).injective
    simpa only [map_one] using heq
  · intro heq
    rw [heq, map_one]

/-- Bare overlap is conjugated; its role differs from the instrument normalizer. -/
theorem overlap_sheetConj (ρ E : SheetMatrix n) :
    overlap (sheetConj ρ) (sheetConj E) = star (overlap ρ E) := by
  unfold overlap
  rw [← map_mul, trace_sheetConj]

/-- Transforming both endpoints and the inserted operator conjugates the complex readout. -/
theorem readout_sheetConj (ρ E A : SheetMatrix n) :
    readout (sheetConj ρ) (sheetConj E) (sheetConj A) = star (readout ρ E A) := by
  unfold readout
  rw [← map_mul, ← map_mul, trace_sheetConj, overlap_sheetConj, star_div₀]

/-- Adding endpoint exchange and probe adjunction restores the original readout. -/
theorem readout_reversed {ρ E : SheetMatrix n}
    (hρ : ρ.IsHermitian) (hE : E.IsHermitian) (A : SheetMatrix n) :
    readout (sheetConj E) (sheetConj ρ) (sheetConj (star A)) = readout ρ E A := by
  rw [readout_sheetConj, star_readout hE hρ, star_star]

end InfoGeometry.Quantum.SemilinearBoundaryReversal
