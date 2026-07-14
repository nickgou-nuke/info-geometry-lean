import Mathlib

noncomputable section

namespace InfoGeometry.Arithmetic.PrimeExteriorRepresentation

open scoped BigOperators

/--
Square-free prime states are represented as finite subsets of prime labels.
This corresponds to the states |n⟩ where n is square-free, represented by the
set of its prime factors.
-/
abbrev SquareFreePrimeState (PrimeLabel : Type*) := Finset PrimeLabel

namespace SquareFreePrimeState

variable {PrimeLabel : Type*} [DecidableEq PrimeLabel]

/-- The total fermion number of a square-free state is the number of its prime factors. -/
def fermionNumber (S : SquareFreePrimeState PrimeLabel) : ℕ :=
  S.card

/-- 
The fermion parity (chirality) of a square-free state.
This is the eigenvalue of the global Gamma operator, and corresponds
to the Möbius function μ(n) for square-free n.
-/
def fermionParitySign (S : SquareFreePrimeState PrimeLabel) : ℤ :=
  (-1 : ℤ) ^ S.card

/-- Global chirality alias for the square-free sector. -/
def Gamma (S : SquareFreePrimeState PrimeLabel) : ℤ :=
  fermionParitySign S

/-- 
The local occupation number of a state.
This represents the action of the local number operator N_p on the state |S⟩.
-/
def localOccupation (p : PrimeLabel) (S : SquareFreePrimeState PrimeLabel) : ℕ :=
  if p ∈ S then 1 else 0

lemma localOccupation_nonneg (p : PrimeLabel) (S : SquareFreePrimeState PrimeLabel) :
    0 ≤ localOccupation p S := by
  unfold localOccupation
  split_ifs <;> norm_num

lemma localOccupation_le_one (p : PrimeLabel) (S : SquareFreePrimeState PrimeLabel) :
    localOccupation p S ≤ 1 := by
  unfold localOccupation
  split_ifs <;> norm_num

/-- Local occupation is `1` exactly when the prime is present in the state. -/
theorem localOccupation_eq_one_iff_mem
    (p : PrimeLabel) (S : SquareFreePrimeState PrimeLabel) :
    localOccupation p S = 1 ↔ p ∈ S := by
  unfold localOccupation
  by_cases h : p ∈ S
  · simp [h]
  · simp [h]

/-- Local occupation is `0` exactly when the prime is absent from the state. -/
theorem localOccupation_eq_zero_iff_not_mem
    (p : PrimeLabel) (S : SquareFreePrimeState PrimeLabel) :
    localOccupation p S = 0 ↔ p ∉ S := by
  unfold localOccupation
  by_cases h : p ∈ S
  · simp [h]
  · simp [h]

/-- 
The local parity of a state.
This represents the action of the local Möbius operator Π_p on the state |S⟩.
-/
def localParitySign (p : PrimeLabel) (S : SquareFreePrimeState PrimeLabel) : ℤ :=
  if p ∈ S then -1 else 1

/-- Local parity is `-1` exactly when the prime is present in the state. -/
theorem localParitySign_eq_neg_one_iff_mem
    (p : PrimeLabel) (S : SquareFreePrimeState PrimeLabel) :
    localParitySign p S = -1 ↔ p ∈ S := by
  unfold localParitySign
  by_cases h : p ∈ S
  · simp [h]
  · simp [h]

/-- Local parity is `+1` exactly when the prime is absent from the state. -/
theorem localParitySign_eq_one_iff_not_mem
    (p : PrimeLabel) (S : SquareFreePrimeState PrimeLabel) :
    localParitySign p S = 1 ↔ p ∉ S := by
  unfold localParitySign
  by_cases h : p ∈ S
  · simp [h]
  · simp [h]

/-- 
The fundamental identity connecting local parity and occupation:
Π_p = 1 - 2N_p evaluated on states.
-/
theorem localParitySign_eq_one_sub_two_localOccupation
    (p : PrimeLabel) (S : SquareFreePrimeState PrimeLabel) :
    localParitySign p S = 1 - 2 * (localOccupation p S : ℤ) := by
  unfold localParitySign localOccupation
  split_ifs
  · norm_num
  · norm_num

/--
Global chirality is the product of local parities on the square-free sector.
This is the diagonal Möbius/Witten readout; the sign-sensitive CAR action is
kept separate.
-/
theorem gamma_eq_prod_localParity
    (S : SquareFreePrimeState PrimeLabel) :
    Gamma S = ∏ p ∈ S, localParitySign p S := by
  classical
  unfold Gamma fermionParitySign localParitySign
  have h_local : ∀ p ∈ S, (if p ∈ S then -1 else 1) = (-1 : ℤ) := by
    intro p hp
    simp [hp]
  calc
    (-1 : ℤ) ^ S.card = ∏ _p ∈ S, (-1 : ℤ) := by
      symm
      exact Finset.prod_const (-1 : ℤ)
    _ = ∏ p ∈ S, localParitySign p S := by
      refine Finset.prod_congr rfl ?_
      intro p hp
      simp [localParitySign, hp]

omit [DecidableEq PrimeLabel] in
/-- The global chirality is the square-free fermion parity `(-1)^F`. -/
theorem Gamma_eq_negOne_pow_fermionNumber
    (S : SquareFreePrimeState PrimeLabel) :
    Gamma S = (-1 : ℤ) ^ fermionNumber S := by
  rfl

/-- 
The energy of a state is the sum of the energies of its occupied modes.
For the arithmetic Hamiltonian, energy p = log p, so this will yield log n.
-/
def squareFreeEnergy
    (energy : PrimeLabel → ℝ)
    (S : SquareFreePrimeState PrimeLabel) : ℝ :=
  ∑ p ∈ S, energy p

omit [DecidableEq PrimeLabel] in
lemma squareFreeEnergy_nonneg
    {energy : PrimeLabel → ℝ}
    (S : SquareFreePrimeState PrimeLabel)
    (henergy : ∀ p ∈ S, 0 ≤ energy p) :
    0 ≤ squareFreeEnergy energy S := by
  unfold squareFreeEnergy
  exact Finset.sum_nonneg (fun p hp => henergy p hp)

end SquareFreePrimeState

end InfoGeometry.Arithmetic.PrimeExteriorRepresentation
