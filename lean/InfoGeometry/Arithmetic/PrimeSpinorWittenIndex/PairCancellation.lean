import Mathlib.Tactic

noncomputable section

open scoped BigOperators

namespace InfoGeometry.Arithmetic.PrimeSpinorWittenIndex

/-! This is plain additive cancellation; no grading, supertrace, or SUSY
index is defined in this file. -/
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
