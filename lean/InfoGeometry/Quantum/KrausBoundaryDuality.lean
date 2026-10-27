/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.Quantum.ChoiCompletePositivity
import Mathlib.LinearAlgebra.Matrix.Trace

/-!
# Noncommutative forward and backward boundary pairing

Finite Kraus maps act on the full matrix algebra. The backward map is the
existing Kraus map at the adjointed family. No commutation or trace-preserving
hypothesis is imposed unless explicitly stated. The trace is a pairing of
operators, not a replacement carrier.
-/

noncomputable section
namespace InfoGeometry.Quantum.Choi

open Matrix
open scoped ComplexOrder

variable {n ι : Type*} [Fintype n] [DecidableEq n] [Fintype ι] [DecidableEq ι]

/-- Cyclic trace identifies the backward Kraus action exactly. -/
theorem trace_krausMap_pairing (V : ι → Matrix n n ℂ) (X E : Matrix n n ℂ) :
    trace (krausMap V X * E) = trace (X * krausMap (fun i => star (V i)) E) := by
  simp only [krausMap, LinearMap.coe_mk, AddHom.coe_mk, Finset.sum_mul,
    Finset.mul_sum, trace_sum, star_star]
  apply Finset.sum_congr rfl
  intro i _
  calc
    trace (V i * X * star (V i) * E) = trace (V i * (X * star (V i) * E)) := by
      simp only [mul_assoc]
    _ = trace ((X * star (V i) * E) * V i) := trace_mul_comm _ _
    _ = trace (X * (star (V i) * E * V i)) := by simp only [mul_assoc]

/-- Every finite Kraus map preserves the positive-semidefinite cone. -/
theorem krausMap_posSemidef (V : ι → Matrix n n ℂ) {X : Matrix n n ℂ}
    (hX : X.PosSemidef) : (krausMap V X).PosSemidef := by
  change (∑ i, V i * X * star (V i)).PosSemidef
  induction (Finset.univ : Finset ι) using Finset.induction_on with
  | empty => simpa using (Matrix.PosSemidef.zero : (0 : Matrix n n ℂ).PosSemidef)
  | @insert i s hi ih =>
      rw [Finset.sum_insert hi]
      exact (hX.mul_mul_conjTranspose_same (V i)).add ih

/-- Trace preservation is equivalent to backward unitality, not an automatic
property of a Kraus family. -/
theorem krausMap_trace_preserving_iff (V : ι → Matrix n n ℂ) :
    (∀ X, trace (krausMap V X) = trace X) ↔
      krausMap (fun i => star (V i)) (1 : Matrix n n ℂ) = 1 := by
  constructor
  · intro h
    apply Matrix.ext_iff_trace_mul_left.mpr
    intro X
    simpa using (trace_krausMap_pairing V X 1).symm.trans (by simpa using h X)
  · intro h X
    simpa [h] using trace_krausMap_pairing V X 1

/-- An operator is conserved against every input exactly when it is fixed
by the backward action. -/
theorem krausMap_conserved_iff (V : ι → Matrix n n ℂ) (E : Matrix n n ℂ) :
    (∀ X, trace (krausMap V X * E) = trace (X * E)) ↔
      krausMap (fun i => star (V i)) E = E := by
  simp_rw [trace_krausMap_pairing]
  exact Matrix.ext_iff_trace_mul_left.symm

/-- Apply a finite word in chronological list order. -/
def forwardWord : List (ι → Matrix n n ℂ) → MatrixMap (n := n)
  | [] => LinearMap.id
  | V :: tail => (forwardWord tail).comp (krausMap V)

/-- Pull an operator backward through the same word, in reverse order. -/
def backwardWord : List (ι → Matrix n n ℂ) → MatrixMap (n := n)
  | [] => LinearMap.id
  | V :: tail => (krausMap (fun i => star (V i))).comp (backwardWord tail)

/-- Finite ordered propagation and backward pullback are trace dual. -/
theorem trace_forwardWord_pairing (word : List (ι → Matrix n n ℂ))
    (X E : Matrix n n ℂ) :
    trace (forwardWord word X * E) = trace (X * backwardWord word E) := by
  induction word generalizing X E with
  | nil => rfl
  | cons V tail ih =>
      change trace (forwardWord tail (krausMap V X) * E) =
        trace (X * krausMap (fun i => star (V i)) (backwardWord tail E))
      rw [ih, trace_krausMap_pairing]

/-- Concatenation composes forward maps in chronological order. -/
theorem forwardWord_append (left right : List (ι → Matrix n n ℂ)) :
    forwardWord (left ++ right) = (forwardWord right).comp (forwardWord left) := by
  induction left with
  | nil => ext X; rfl
  | cons V tail ih =>
      simp only [List.cons_append, forwardWord, ih, LinearMap.comp_assoc]

/-- Backward maps compose contravariantly. -/
theorem backwardWord_append (left right : List (ι → Matrix n n ℂ)) :
    backwardWord (left ++ right) = (backwardWord left).comp (backwardWord right) := by
  induction left with
  | nil => ext X; rfl
  | cons V tail ih =>
      simp only [List.cons_append, backwardWord, ih, LinearMap.comp_assoc]

/-- Every cut of a word has the same boundary pairing. -/
theorem trace_pairing_at_cut (left right : List (ι → Matrix n n ℂ))
    (X E : Matrix n n ℂ) :
    trace (forwardWord left X * backwardWord right E) =
      trace (forwardWord (left ++ right) X * E) := by
  rw [forwardWord_append, LinearMap.comp_apply]
  exact (trace_forwardWord_pairing right (forwardWord left X) E).symm

/-- The native ordered set of cuts is `Fin (word.length + 1)`.
The boundary pairing is constant at every such cut. -/
theorem trace_pairing_at_index (word : List (ι → Matrix n n ℂ))
    (cut : Fin (word.length + 1)) (X E : Matrix n n ℂ) :
    trace (forwardWord (word.take cut.val) X * backwardWord (word.drop cut.val) E) =
      trace (forwardWord word X * E) := by
  simpa only [List.take_append_drop] using
    trace_pairing_at_cut (word.take cut.val) (word.drop cut.val) X E

/-- Positive boundary data stays positive under finite forward propagation. -/
theorem forwardWord_posSemidef (word : List (ι → Matrix n n ℂ))
    {X : Matrix n n ℂ} (hX : X.PosSemidef) : (forwardWord word X).PosSemidef := by
  induction word generalizing X with
  | nil => exact hX
  | cons V tail ih => exact ih (krausMap_posSemidef V hX)

/-- Positive boundary data stays positive under finite backward propagation. -/
theorem backwardWord_posSemidef (word : List (ι → Matrix n n ℂ))
    {E : Matrix n n ℂ} (hE : E.PosSemidef) : (backwardWord word E).PosSemidef := by
  induction word with
  | nil => exact hE
  | cons V tail ih => exact krausMap_posSemidef _ ih

end InfoGeometry.Quantum.Choi
