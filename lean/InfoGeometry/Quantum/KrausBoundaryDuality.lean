/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.Quantum.ChoiCompletePositivity
import Mathlib.LinearAlgebra.Matrix.Trace
import Mathlib.Data.Matrix.PEquiv
import Mathlib.GroupTheory.Perm.Basic

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
  | cons V tail ih => exact krausMap_posSemidef (fun i => star (V i)) ih

/-! ## Unitary mixtures as noncommutative Birkhoff channels -/

/-- The operator matrix associated with a finite permutation. -/
def permutationOperator (σ : Equiv.Perm n) : Matrix n n ℂ :=
  σ.toPEquiv.toMatrix

/-- Permutation operators are unitary on the full matrix-operator carrier. -/
theorem permutationOperator_unitary (σ : Equiv.Perm n) :
    permutationOperator σ * star (permutationOperator σ) = 1 ∧
      star (permutationOperator σ) * permutationOperator σ = 1 := by
  have hstar : star (permutationOperator σ) = (permutationOperator σ)ᵀ := by
    ext i j
    simp [permutationOperator]
  constructor
  · rw [hstar]
    ext i j
    simp only [permutationOperator, Matrix.mul_apply, PEquiv.toMatrix_apply]
    rw [Finset.sum_eq_single (σ j)]
    · have hσ : σ i = σ j ↔ i = j := σ.injective.eq_iff
      simp [hσ, Matrix.one_apply]
    · intro k hk hne
      have hkj : σ j ≠ k := by
        intro h
        apply hne
        exact h.symm
      simp [hkj]
    · simp
  · rw [hstar]
    ext i j
    simp only [permutationOperator, Matrix.mul_apply, PEquiv.toMatrix_apply]
    rw [Finset.sum_eq_single (σ.symm j)]
    · simp [Equiv.apply_symm_apply, Matrix.one_apply, eq_comm]
    · intro k hk hne
      have hkj : σ k ≠ j := by
        intro h
        apply hne
        exact σ.injective (h.trans (Equiv.apply_symm_apply σ j).symm)
      simp [hkj]
    · simp

/-- A weighted mixture of unitary conjugations on the full matrix algebra.
The weights are scalar probabilities, while each summand acts by genuine
noncommuting operator multiplication. -/
def unitaryMixtureChannel {κ : Type*} [Fintype κ] [DecidableEq κ]
    (w : κ → ℝ) (U : κ → Matrix n n ℂ) (X : Matrix n n ℂ) : Matrix n n ℂ :=
  ∑ i, (w i : ℂ) • (U i * X * star (U i))

/-- A normalized finite mixture of two-sided unitary conjugations is both
unital and trace-preserving on the full, noncommutative matrix algebra. -/
theorem unitaryMixtureChannel_doubly_stochastic
    {κ : Type*} [Fintype κ] [DecidableEq κ]
    (w : κ → ℝ) (hw : ∑ i, w i = 1)
    (U : κ → Matrix n n ℂ)
    (hU : ∀ i, U i * star (U i) = 1 ∧ star (U i) * U i = 1)
    (X : Matrix n n ℂ) :
    unitaryMixtureChannel w U 1 = 1 ∧
      trace (unitaryMixtureChannel w U X) = trace X := by
  constructor
  · unfold unitaryMixtureChannel
    have hwC : ∑ i, (w i : ℂ) = 1 := by exact_mod_cast hw
    have hterm : ∀ i, U i * (1 : Matrix n n ℂ) * star (U i) = 1 := by
      intro i
      rw [Matrix.mul_one, (hU i).1]
    simp_rw [hterm]
    rw [← Finset.sum_smul, hwC, one_smul]
  · unfold unitaryMixtureChannel
    rw [trace_sum]
    have hwC : ∑ i, (w i : ℂ) = 1 := by exact_mod_cast hw
    have hterm : ∀ i,
        trace ((w i : ℂ) • (U i * X * star (U i))) =
          (w i : ℂ) • trace X := by
      intro i
      rw [trace_smul]
      calc
        (w i : ℂ) • trace (U i * X * star (U i)) =
            (w i : ℂ) • trace (star (U i) * (U i * X)) := by
          rw [Matrix.trace_mul_comm (U i * X) (star (U i))]
        _ = (w i : ℂ) • trace ((star (U i) * U i) * X) := by
          rw [← mul_assoc]
        _ = (w i : ℂ) • trace X := by rw [(hU i).2, Matrix.one_mul]
    simp_rw [hterm, ← Finset.sum_smul, hwC, one_smul]

end InfoGeometry.Quantum.Choi
