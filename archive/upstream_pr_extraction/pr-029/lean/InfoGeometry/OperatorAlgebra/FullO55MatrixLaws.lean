import Mathlib.Tactic

/-!
# Full finite O(5,5) matrix laws

This module is the Lean twin of `tools/sympy/full_o55_matrix_laws.py`.
It gives a native finite matrix owner surface for the split form
`η = diag(1,1,1,1,1,-1,-1,-1,-1,-1)`.

#### BUCKET 1: CLOSED FINITE THEOREMS
The declarations below kernel-check the complete split-block Lie algebra basis:

* `rotPlus_all_so55`: all `so(5)` generators in the positive block are in `so(5,5)`;
* `rotMinus_all_so55`: all `so(5)` generators in the negative block are in `so(5,5)`;
* `boost_all_so55`: all 25 mixed boost generators are in `so(5,5)`;
* `cartan_commutes`: the five diagonal boost generators commute;
* `pairSwap01_is_o55`, `evenSignFlip01_is_o55`, `singleSignFlip0_is_o55`:
  concrete disconnected ambient `O(5,5)` matrix representatives;
* `lightlikePlus_null`, `lightlikeMinus_null`, `lightlike_pairing`: the five split
  coordinate pairs give null light-cone directions.

#### BUCKET 3: OPEN CLOSURE DEBT
This file does not prove Pin(5,5) lift data, spinor representation classification,
triality outer automorphisms, analytic continuation, or bulk reconstruction.
-/

namespace InfoGeometry.OperatorAlgebra.FullO55MatrixLaws

open Matrix

abbrev M10Z := Matrix (Fin 10) (Fin 10) ℤ
abbrev V10Z := Fin 10 → ℤ

/-- Positive coordinate inclusion `0..4 ↪ 0..9`. -/
def posIndex (i : Fin 5) : Fin 10 := ⟨i.val, by omega⟩

/-- Negative coordinate inclusion `0..4 ↦ 5..9`. -/
def negIndex (i : Fin 5) : Fin 10 := ⟨i.val + 5, by omega⟩

/-- Matrix unit `E_{ij}` over `ℤ`. -/
def unit (i j : Fin 10) : M10Z := fun r c => if r = i ∧ c = j then 1 else 0

/-- Coordinate vector `e_i` over `ℤ`. -/
def basisVec (i : Fin 10) : V10Z := fun r => if r = i then 1 else 0

/-- Split `O(5,5)` metric `diag(1,1,1,1,1,-1,-1,-1,-1,-1)`. -/
def eta : M10Z :=
  !![1, 0, 0, 0, 0, 0, 0, 0, 0, 0;
     0, 1, 0, 0, 0, 0, 0, 0, 0, 0;
     0, 0, 1, 0, 0, 0, 0, 0, 0, 0;
     0, 0, 0, 1, 0, 0, 0, 0, 0, 0;
     0, 0, 0, 0, 1, 0, 0, 0, 0, 0;
     0, 0, 0, 0, 0, -1, 0, 0, 0, 0;
     0, 0, 0, 0, 0, 0, -1, 0, 0, 0;
     0, 0, 0, 0, 0, 0, 0, -1, 0, 0;
     0, 0, 0, 0, 0, 0, 0, 0, -1, 0;
     0, 0, 0, 0, 0, 0, 0, 0, 0, -1]

/-- Orthogonal group predicate for the fixed split form. -/
def IsO55 (A : M10Z) : Prop := Aᵀ * eta * A = eta

/-- Split orthogonal Lie algebra predicate for the fixed split form. -/
def IsSO55Lie (X : M10Z) : Prop := Xᵀ * eta + eta * X = 0

/-- Matrix commutator. -/
def comm (A B : M10Z) : M10Z := A * B - B * A

/-- Positive-block rotation generator. -/
def rotPlus (i j : Fin 5) : M10Z :=
  unit (posIndex i) (posIndex j) - unit (posIndex j) (posIndex i)

/-- Negative-block rotation generator. -/
def rotMinus (i j : Fin 5) : M10Z :=
  unit (negIndex i) (negIndex j) - unit (negIndex j) (negIndex i)

/-- Mixed split boost generator. -/
def boost (i j : Fin 5) : M10Z :=
  unit (posIndex i) (negIndex j) + unit (negIndex j) (posIndex i)

/-- `η² = I`, the split metric is involutive. -/
theorem eta_sq : eta * eta = 1 := by
  native_decide

/-- The positive-block antisymmetric generators all satisfy `Xᵀ η + η X = 0`. -/
theorem rotPlus_all_so55 : ∀ i j : Fin 5, IsSO55Lie (rotPlus i j) := by
  intro i j
  fin_cases i <;> fin_cases j <;> unfold IsSO55Lie rotPlus unit posIndex eta <;> native_decide

/-- The negative-block antisymmetric generators all satisfy `Xᵀ η + η X = 0`. -/
theorem rotMinus_all_so55 : ∀ i j : Fin 5, IsSO55Lie (rotMinus i j) := by
  intro i j
  fin_cases i <;> fin_cases j <;> unfold IsSO55Lie rotMinus unit negIndex eta <;> native_decide

/-- The 25 mixed boost generators all satisfy `Xᵀ η + η X = 0`. -/
theorem boost_all_so55 : ∀ i j : Fin 5, IsSO55Lie (boost i j) := by
  intro i j
  fin_cases i <;> fin_cases j <;>
    unfold IsSO55Lie boost unit posIndex negIndex eta <;> native_decide

/-- The five diagonal boosts are a commuting split Cartan subalgebra. -/
theorem cartan_commutes : ∀ i j : Fin 5, comm (boost i i) (boost j j) = 0 := by
  intro i j
  fin_cases i <;> fin_cases j <;>
    unfold comm boost unit posIndex negIndex <;> native_decide

/-- A coordinate-pair swap, exchanging the first two positive and negative coordinates. -/
def pairSwap01 : M10Z :=
  !![0, 1, 0, 0, 0, 0, 0, 0, 0, 0;
     1, 0, 0, 0, 0, 0, 0, 0, 0, 0;
     0, 0, 1, 0, 0, 0, 0, 0, 0, 0;
     0, 0, 0, 1, 0, 0, 0, 0, 0, 0;
     0, 0, 0, 0, 1, 0, 0, 0, 0, 0;
     0, 0, 0, 0, 0, 0, 1, 0, 0, 0;
     0, 0, 0, 0, 0, 1, 0, 0, 0, 0;
     0, 0, 0, 0, 0, 0, 0, 1, 0, 0;
     0, 0, 0, 0, 0, 0, 0, 0, 1, 0;
     0, 0, 0, 0, 0, 0, 0, 0, 0, 1]

/-- A coordinate-pair swap is an `O(5,5)` matrix. -/
theorem pairSwap01_is_o55 : IsO55 pairSwap01 := by
  unfold IsO55
  native_decide

/-- Even sign flip on the first two positive and negative coordinate pairs. -/
def evenSignFlip01 : M10Z :=
  !![-1, 0, 0, 0, 0, 0, 0, 0, 0, 0;
      0,-1, 0, 0, 0, 0, 0, 0, 0, 0;
      0, 0, 1, 0, 0, 0, 0, 0, 0, 0;
      0, 0, 0, 1, 0, 0, 0, 0, 0, 0;
      0, 0, 0, 0, 1, 0, 0, 0, 0, 0;
      0, 0, 0, 0, 0,-1, 0, 0, 0, 0;
      0, 0, 0, 0, 0, 0,-1, 0, 0, 0;
      0, 0, 0, 0, 0, 0, 0, 1, 0, 0;
      0, 0, 0, 0, 0, 0, 0, 0, 1, 0;
      0, 0, 0, 0, 0, 0, 0, 0, 0, 1]

/-- The even coordinate-pair sign flip is an `O(5,5)` matrix. -/
theorem evenSignFlip01_is_o55 : IsO55 evenSignFlip01 := by
  unfold IsO55
  native_decide

/-- A one-coordinate sign flip, witnessing the larger disconnected ambient group. -/
def singleSignFlip0 : M10Z :=
  !![-1, 0, 0, 0, 0, 0, 0, 0, 0, 0;
      0, 1, 0, 0, 0, 0, 0, 0, 0, 0;
      0, 0, 1, 0, 0, 0, 0, 0, 0, 0;
      0, 0, 0, 1, 0, 0, 0, 0, 0, 0;
      0, 0, 0, 0, 1, 0, 0, 0, 0, 0;
      0, 0, 0, 0, 0, 1, 0, 0, 0, 0;
      0, 0, 0, 0, 0, 0, 1, 0, 0, 0;
      0, 0, 0, 0, 0, 0, 0, 1, 0, 0;
      0, 0, 0, 0, 0, 0, 0, 0, 1, 0;
      0, 0, 0, 0, 0, 0, 0, 0, 0, 1]

/-- A single coordinate sign flip is still an `O(5,5)` matrix. -/
theorem singleSignFlip0_is_o55 : IsO55 singleSignFlip0 := by
  unfold IsO55
  native_decide

/-- Bilinear form associated to `η`. -/
def etaPair (x y : V10Z) : ℤ := dotProduct x (eta.mulVec y)

/-- Positive light-cone vector `e_i + f_i`. -/
def lightlikePlus (i : Fin 5) : V10Z := basisVec (posIndex i) + basisVec (negIndex i)

/-- Negative light-cone vector `e_i - f_i`. -/
def lightlikeMinus (i : Fin 5) : V10Z := basisVec (posIndex i) - basisVec (negIndex i)

/-- Every `e_i + f_i` is null for the split form. -/
theorem lightlikePlus_null : ∀ i : Fin 5, etaPair (lightlikePlus i) (lightlikePlus i) = 0 := by
  native_decide

/-- Every `e_i - f_i` is null for the split form. -/
theorem lightlikeMinus_null : ∀ i : Fin 5, etaPair (lightlikeMinus i) (lightlikeMinus i) = 0 := by
  native_decide

/-- The paired null directions have split pairing `2`. -/
theorem lightlike_pairing : ∀ i : Fin 5, etaPair (lightlikePlus i) (lightlikeMinus i) = 2 := by
  native_decide

/-- Finite count of the full split-block basis: `10 + 10 + 25 = 45`. -/
theorem full_so55_basis_count : 5 * 4 / 2 + 5 * 4 / 2 + 5 * 5 = 45 := by
  native_decide

/-- Finite D5 root count: the 45-dimensional Lie algebra has 5 Cartan and 40 roots. -/
theorem d5_root_count_shadow : 45 - 5 = 40 := by
  native_decide

/-- Closed finite packet for the full O(5,5) matrix-law owner surface. -/
theorem full_o55_matrix_law_packet :
    eta * eta = 1 ∧
      (∀ i j : Fin 5, IsSO55Lie (rotPlus i j)) ∧
      (∀ i j : Fin 5, IsSO55Lie (rotMinus i j)) ∧
      (∀ i j : Fin 5, IsSO55Lie (boost i j)) ∧
      (∀ i j : Fin 5, comm (boost i i) (boost j j) = 0) ∧
      IsO55 pairSwap01 ∧ IsO55 evenSignFlip01 ∧ IsO55 singleSignFlip0 ∧
      (∀ i : Fin 5, etaPair (lightlikePlus i) (lightlikePlus i) = 0) ∧
      (∀ i : Fin 5, etaPair (lightlikeMinus i) (lightlikeMinus i) = 0) ∧
      (∀ i : Fin 5, etaPair (lightlikePlus i) (lightlikeMinus i) = 2) := by
  exact ⟨eta_sq, rotPlus_all_so55, rotMinus_all_so55, boost_all_so55,
    cartan_commutes, pairSwap01_is_o55, evenSignFlip01_is_o55,
    singleSignFlip0_is_o55, lightlikePlus_null, lightlikeMinus_null,
    lightlike_pairing⟩

end InfoGeometry.OperatorAlgebra.FullO55MatrixLaws
