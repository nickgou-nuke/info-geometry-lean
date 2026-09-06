import Mathlib.Tactic

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

end InfoGeometry.Arithmetic.PrimeSpinorWittenIndex
