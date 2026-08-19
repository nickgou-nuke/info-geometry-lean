import Mathlib.Tactic

noncomputable section

namespace InfoGeometry.Arithmetic.PrimeExteriorRepresentation

open scoped BigOperators

abbrev SquareFreePrimeState (PrimeLabel : Type*) := Finset PrimeLabel

/-! ## Finite Boolean-coordinate form of the exterior carrier -/

/-
The square-free carrier is a finite subset carrier.  When the label type is
finite, its Boolean-coordinate presentation is an actual equivalence, not a
second algebra or a colimit interface.
-/

def toBooleanCoordinates {PrimeLabel : Type*} [DecidableEq PrimeLabel]
    (S : SquareFreePrimeState PrimeLabel) : PrimeLabel → Bool :=
  fun p => decide (p ∈ S)

def ofBooleanCoordinates {PrimeLabel : Type*} [Fintype PrimeLabel]
    (b : PrimeLabel → Bool) : SquareFreePrimeState PrimeLabel :=
  Finset.univ.filter (fun p => b p = true)

def booleanCoordinatesEquiv (PrimeLabel : Type*) [Fintype PrimeLabel]
    [DecidableEq PrimeLabel] :
    SquareFreePrimeState PrimeLabel ≃ (PrimeLabel → Bool) where
  toFun := toBooleanCoordinates
  invFun := ofBooleanCoordinates
  left_inv := by
    intro S
    ext p
    simp [toBooleanCoordinates, ofBooleanCoordinates]
  right_inv := by
    intro b
    funext p
    simp [toBooleanCoordinates, ofBooleanCoordinates]

@[simp] theorem booleanCoordinatesEquiv_apply_mem
    {PrimeLabel : Type*} [Fintype PrimeLabel] [DecidableEq PrimeLabel]
    (S : SquareFreePrimeState PrimeLabel) (p : PrimeLabel) :
    booleanCoordinatesEquiv PrimeLabel S p = decide (p ∈ S) := rfl

@[simp] theorem booleanCoordinatesEquiv_symm_apply
    {PrimeLabel : Type*} [Fintype PrimeLabel] [DecidableEq PrimeLabel]
    (b : PrimeLabel → Bool) :
    (booleanCoordinatesEquiv PrimeLabel).symm b =
      Finset.univ.filter (fun p => b p = true) := rfl

theorem card_squareFreePrimeState
    (PrimeLabel : Type*) [Fintype PrimeLabel] [DecidableEq PrimeLabel] :
    Fintype.card (SquareFreePrimeState PrimeLabel) =
      2 ^ Fintype.card PrimeLabel := by
  simpa [Fintype.card_fun, Fintype.card_bool] using
    Fintype.card_congr (booleanCoordinatesEquiv PrimeLabel)

namespace SquareFreePrimeState

variable {PrimeLabel : Type*} [DecidableEq PrimeLabel]

def fermionNumber (S : SquareFreePrimeState PrimeLabel) : ℕ :=
  S.card

def fermionParitySign (S : SquareFreePrimeState PrimeLabel) : ℤ :=
  (-1 : ℤ) ^ S.card

def Gamma (S : SquareFreePrimeState PrimeLabel) : ℤ :=
  fermionParitySign S

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

theorem localOccupation_eq_one_iff_mem
    (p : PrimeLabel) (S : SquareFreePrimeState PrimeLabel) :
    localOccupation p S = 1 ↔ p ∈ S := by
  unfold localOccupation
  by_cases h : p ∈ S
  · simp [h]
  · simp [h]

theorem localOccupation_eq_zero_iff_not_mem
    (p : PrimeLabel) (S : SquareFreePrimeState PrimeLabel) :
    localOccupation p S = 0 ↔ p ∉ S := by
  unfold localOccupation
  by_cases h : p ∈ S
  · simp [h]
  · simp [h]

def localParitySign (p : PrimeLabel) (S : SquareFreePrimeState PrimeLabel) : ℤ :=
  if p ∈ S then -1 else 1

theorem localParitySign_eq_neg_one_iff_mem
    (p : PrimeLabel) (S : SquareFreePrimeState PrimeLabel) :
    localParitySign p S = -1 ↔ p ∈ S := by
  unfold localParitySign
  by_cases h : p ∈ S
  · simp [h]
  · simp [h]

theorem localParitySign_eq_one_iff_not_mem
    (p : PrimeLabel) (S : SquareFreePrimeState PrimeLabel) :
    localParitySign p S = 1 ↔ p ∉ S := by
  unfold localParitySign
  by_cases h : p ∈ S
  · simp [h]
  · simp [h]

theorem localParitySign_eq_one_sub_two_localOccupation
    (p : PrimeLabel) (S : SquareFreePrimeState PrimeLabel) :
    localParitySign p S = 1 - 2 * (localOccupation p S : ℤ) := by
  unfold localParitySign localOccupation
  split_ifs
  · norm_num
  · norm_num

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
theorem Gamma_eq_negOne_pow_fermionNumber
    (S : SquareFreePrimeState PrimeLabel) :
    Gamma S = (-1 : ℤ) ^ fermionNumber S := by
  rfl

omit [DecidableEq PrimeLabel] in
theorem Gamma_mul_self (S : SquareFreePrimeState PrimeLabel) :
    Gamma S * Gamma S = 1 := by
  rw [Gamma_eq_negOne_pow_fermionNumber]
  rw [← pow_add]
  have hpow : (-1 : ℤ) ^ (S.card + S.card) = 1 := by
    rw [show S.card + S.card = 2 * S.card by omega]
    rw [pow_mul]
    norm_num
  exact hpow

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
