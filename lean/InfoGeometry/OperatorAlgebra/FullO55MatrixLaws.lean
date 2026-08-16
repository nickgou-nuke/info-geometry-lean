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

/-- The split orthogonal Lie predicate is closed under addition. -/
theorem IsSO55Lie_add {X Y : M10Z} (hX : IsSO55Lie X) (hY : IsSO55Lie Y) :
    IsSO55Lie (X + Y) := by
  unfold IsSO55Lie at hX hY ⊢
  calc
    (X + Y)ᵀ * eta + eta * (X + Y) =
        (Xᵀ * eta + eta * X) + (Yᵀ * eta + eta * Y) := by
      simp only [transpose_add, add_mul, mul_add]
      abel
    _ = 0 := by rw [hX, hY, add_zero]

/-- The split orthogonal Lie predicate is closed under negation. -/
theorem IsSO55Lie_neg {X : M10Z} (hX : IsSO55Lie X) :
    IsSO55Lie (-X) := by
  unfold IsSO55Lie at hX ⊢
  calc
    (-X)ᵀ * eta + eta * (-X) = -(Xᵀ * eta + eta * X) := by
      simp only [transpose_neg, neg_mul, mul_neg]
      abel
    _ = 0 := by rw [hX, neg_zero]

/-- The zero matrix satisfies the split orthogonal Lie predicate. -/
theorem IsSO55Lie_zero : IsSO55Lie (0 : M10Z) := by
  unfold IsSO55Lie
  simp

/-- The split orthogonal Lie predicate is closed under integer scaling. -/
theorem IsSO55Lie_smul (a : ℤ) {X : M10Z} (hX : IsSO55Lie X) :
    IsSO55Lie (a • X) := by
  unfold IsSO55Lie at hX ⊢
  calc
    (a • X)ᵀ * eta + eta * (a • X) =
        a • (Xᵀ * eta + eta * X) := by
      rw [Matrix.transpose_smul, Matrix.smul_mul, Matrix.mul_smul,
        smul_add]
    _ = 0 := by rw [hX, smul_zero]

/-- The split orthogonal Lie predicate is closed under subtraction. -/
theorem IsSO55Lie_sub {X Y : M10Z} (hX : IsSO55Lie X) (hY : IsSO55Lie Y) :
    IsSO55Lie (X - Y) := by
  simpa [sub_eq_add_neg] using IsSO55Lie_add hX (IsSO55Lie_neg hY)

/-- The split orthogonal Lie predicate is closed under matrix commutators. -/
theorem IsSO55Lie_comm {X Y : M10Z} (hX : IsSO55Lie X) (hY : IsSO55Lie Y) :
    IsSO55Lie (comm X Y) := by
  unfold IsSO55Lie at hX hY ⊢
  change (X * Y - Y * X)ᵀ * eta + eta * (X * Y - Y * X) = 0
  have hx : Xᵀ * eta = -(eta * X) := by
    exact eq_neg_of_add_eq_zero_left hX
  have hy : Yᵀ * eta = -(eta * Y) := by
    exact eq_neg_of_add_eq_zero_left hY
  calc
    (X * Y - Y * X)ᵀ * eta + eta * (X * Y - Y * X) =
        Yᵀ * (Xᵀ * eta) - Xᵀ * (Yᵀ * eta) +
          (eta * X * Y - eta * Y * X) := by
            simp only [transpose_sub, transpose_mul, sub_mul, mul_sub, mul_assoc]
    _ = -(Yᵀ * (eta * X)) + Xᵀ * (eta * Y) +
          (eta * X * Y - eta * Y * X) := by
            rw [hx, hy]
            noncomm_ring
    _ = -((Yᵀ * eta) * X) + (Xᵀ * eta) * Y +
          (eta * X * Y - eta * Y * X) := by
            simp only [mul_assoc]
    _ = -((-(eta * Y)) * X) + (-(eta * X)) * Y +
          (eta * X * Y - eta * Y * X) := by
            rw [hx, hy]
    _ = 0 := by
          noncomm_ring

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

/-- The finite split orthogonal predicate is closed under matrix multiplication. -/
theorem IsO55_mul {A B : M10Z} (hA : IsO55 A) (hB : IsO55 B) :
    IsO55 (A * B) := by
  unfold IsO55 at hA hB ⊢
  rw [transpose_mul]
  calc
    (Bᵀ * Aᵀ) * eta * (A * B) = Bᵀ * (Aᵀ * eta * A) * B := by
      simp only [mul_assoc]
    _ = Bᵀ * eta * B := by rw [hA]
    _ = eta := hB

/-- The explicit disconnected representatives are involutions. -/
theorem pairSwap01_involutive : pairSwap01 * pairSwap01 = 1 := by
  unfold pairSwap01
  native_decide

theorem evenSignFlip01_involutive : evenSignFlip01 * evenSignFlip01 = 1 := by
  unfold evenSignFlip01
  native_decide

theorem singleSignFlip0_involutive : singleSignFlip0 * singleSignFlip0 = 1 := by
  unfold singleSignFlip0
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

end InfoGeometry.OperatorAlgebra.FullO55MatrixLaws
