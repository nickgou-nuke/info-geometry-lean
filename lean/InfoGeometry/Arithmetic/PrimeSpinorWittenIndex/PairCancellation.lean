/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import Mathlib.Tactic
import InfoGeometry.Algebra.FiniteSpinAlgebra

noncomputable section

open scoped BigOperators

namespace InfoGeometry.Arithmetic.PrimeSpinorWittenIndex

def pairedWittenContribution
  {R : Type*} [Sub R]
  (weight : R) : R :=
  weight - weight

@[simp]
theorem pairedWittenContribution_eq_zero
  {R : Type*} [AddGroup R]
  (weight : R) :
  pairedWittenContribution weight = 0 := by
  unfold pairedWittenContribution
  simp

theorem finitePairedWittenContributions_sum_eq_zero
  {PairLabel R : Type*} [AddCommGroup R]
  (pairs : Finset PairLabel)
  (weight : PairLabel → R) :
  Finset.sum pairs (fun a => pairedWittenContribution (weight a)) = 0 := by
  simp

def pairedCancellation
  {R : Type*} [Sub R]
  (weight : R) : R :=
  weight - weight

@[simp]

theorem pairedCancellation_eq_zero
  {R : Type*} [AddGroup R]
  (weight : R) :
  pairedCancellation weight = 0 := by
  unfold pairedCancellation
  simp


theorem finitePairedCancellations_sum_eq_zero
  {PairLabel R : Type*} [AddCommGroup R]
  (pairs : Finset PairLabel)
  (weight : PairLabel → R) :
  Finset.sum pairs (fun a => pairedCancellation (weight a)) = 0 := by
  simp

end InfoGeometry.Arithmetic.PrimeSpinorWittenIndex
