import Mathlib.Tactic

/-!
# CAR / CCR / Cantor Fock Layer

This module separates the two local Fock geometries used by the arithmetic
construction.

* CAR: one fermionic mode has occupation `{0,1}`.  Finite CAR words are
  `Fin n → Bool`, and the infinite diagonal readout is the Cantor boundary
  `ℕ → Bool`.
* CCR: one bosonic mode has occupation `ℕ`.  Finite CCR words are
  `Fin n → ℕ`, and finite cutoff words are `Fin n → Fin (K+1)`.

The finite partition factors are:

* ordinary CAR: `1 + x`;
* graded CAR: `1 - x`;
* CCR cutoff: `Σ_{k≤K} x^k`;
* formal CCR/boson determinant: `(1-x)⁻¹`.

The exact CAR one-mode seed is realized by `2×2` matrices.
-/

noncomputable section

namespace CARCCRCantorFock

open Matrix

/-- Finite CAR/Fermion Fock words: one Boolean occupation per mode. -/
abbrev CARWord (n : ℕ) : Type :=
  Fin n → Bool

/-- Infinite CAR diagonal readout: Cantor boundary. -/
abbrev CantorBoundary : Type :=
  ℕ → Bool

/-- Finite CCR/Boson Fock words: one natural occupation per mode. -/
abbrev CCRWord (n : ℕ) : Type :=
  Fin n → ℕ

/-- Infinite CCR occupation readout. -/
abbrev BaireBoundary : Type :=
  ℕ → ℕ

/-- Finite CCR cutoff words with occupations `0,...,K`. -/
abbrev CCRCutoffWord (n K : ℕ) : Type :=
  Fin n → Fin (K + 1)

instance (n : ℕ) : Fintype (CARWord n) := by
  infer_instance

instance (n K : ℕ) : Fintype (CCRCutoffWord n K) := by
  infer_instance

theorem carWord_card (n : ℕ) :
    Fintype.card (CARWord n) = 2 ^ n := by
  simp [CARWord]

theorem ccrCutoffWord_card (n K : ℕ) :
    Fintype.card (CCRCutoffWord n K) = (K + 1) ^ n := by
  simp [CCRCutoffWord]

/-- CAR annihilation matrix for one fermion mode. -/
def carAnnihilate : Matrix (Fin 2) (Fin 2) ℂ :=
  !![0, 1;
     0, 0]

/-- CAR creation matrix for one fermion mode. -/
def carCreate : Matrix (Fin 2) (Fin 2) ℂ :=
  !![0, 0;
     1, 0]

/-- Fermion number projection. -/
def carNumber : Matrix (Fin 2) (Fin 2) ℂ :=
  carCreate * carAnnihilate

/-- Fermion parity operator `(-1)^F = 1 - 2N`. -/
def carParity : Matrix (Fin 2) (Fin 2) ℂ :=
  1 - (2 : ℂ) • carNumber

theorem carAnnihilate_sq :
    carAnnihilate * carAnnihilate = 0 := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [carAnnihilate, Matrix.mul_apply, Fin.sum_univ_two]

theorem carCreate_sq :
    carCreate * carCreate = 0 := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [carCreate, Matrix.mul_apply, Fin.sum_univ_two]

theorem car_anticommutator :
    carAnnihilate * carCreate + carCreate * carAnnihilate =
      (1 : Matrix (Fin 2) (Fin 2) ℂ) := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [carAnnihilate, carCreate]

theorem carNumber_idempotent :
    carNumber * carNumber = carNumber := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [carNumber, carAnnihilate, carCreate, Matrix.mul_apply, Fin.sum_univ_two]

theorem carParity_sq :
    carParity * carParity = (1 : Matrix (Fin 2) (Fin 2) ℂ) := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [carParity, carNumber, carAnnihilate, carCreate, Matrix.mul_apply, Fin.sum_univ_two]

/-- Ordinary CAR local partition factor. -/
def carOrdinaryLocal (x : ℂ) : ℂ :=
  1 + x

/-- Graded CAR local supertrace factor. -/
def carGradedLocal (x : ℂ) : ℂ :=
  1 - x

/-- Formal CCR/bosonic local determinant factor. -/
def ccrFormalLocal (x : ℂ) : ℂ :=
  (1 - x)⁻¹

/-- Finite CCR cutoff local partition factor `Σ_{k=0}^K x^k`. -/
def ccrCutoffLocal (x : ℂ) (K : ℕ) : ℂ :=
  (Finset.range (K + 1)).sum fun k => x ^ k

def carOrdinaryPartition (xs : List ℂ) : ℂ :=
  xs.map carOrdinaryLocal |>.prod

def carGradedPartition (xs : List ℂ) : ℂ :=
  xs.map carGradedLocal |>.prod

def ccrFormalPartition (xs : List ℂ) : ℂ :=
  xs.map ccrFormalLocal |>.prod

def ccrCutoffPartition (xs : List ℂ) (K : ℕ) : ℂ :=
  xs.map (fun x => ccrCutoffLocal x K) |>.prod

theorem ccrCutoffLocal_zero (x : ℂ) :
    ccrCutoffLocal x 0 = 1 := by
  simp [ccrCutoffLocal]

theorem ccrCutoffLocal_succ (x : ℂ) (K : ℕ) :
    ccrCutoffLocal x (K + 1) = ccrCutoffLocal x K + x ^ (K + 1) := by
  simp [ccrCutoffLocal, Finset.sum_range_succ]

theorem ccrFormal_cancels_carGraded {x : ℂ} (hx : x ≠ 1) :
    ccrFormalLocal x * carGradedLocal x = 1 := by
  have hden : 1 - x ≠ 0 := sub_ne_zero.mpr (Ne.symm hx)
  simp [ccrFormalLocal, carGradedLocal, hden]

theorem ccrFormalPartition_cancels_carGraded
    (xs : List ℂ) (hxs : ∀ x ∈ xs, x ≠ 1) :
    ccrFormalPartition xs * carGradedPartition xs = 1 := by
  induction xs with
  | nil =>
      simp [ccrFormalPartition, carGradedPartition]
  | cons x xs ih =>
      have hx : x ≠ 1 := hxs x (by simp)
      have htail : ∀ y ∈ xs, y ≠ 1 := by
        intro y hy
        exact hxs y (by simp [hy])
      calc
        ccrFormalPartition (x :: xs) * carGradedPartition (x :: xs)
            =
          ((1 - x)⁻¹ * ccrFormalPartition xs) *
            ((1 - x) * carGradedPartition xs) := by
              rfl
        _ =
          ((1 - x)⁻¹ * (1 - x)) *
            (ccrFormalPartition xs * carGradedPartition xs) := by
              ring
        _ = 1 * 1 := by
              rw [ih htail]
              exact congrArg (fun a => a * 1) (by
                have hden : 1 - x ≠ 0 := sub_ne_zero.mpr (Ne.symm hx)
                simp [hden])
        _ = 1 := by ring

theorem carOrdinaryLocal_eq_bool_trace (x : ℂ) :
    (if false then x else 1) + (if true then x else 1) = carOrdinaryLocal x := by
  simp [carOrdinaryLocal]

theorem carGradedLocal_eq_bool_supertrace (x : ℂ) :
    (if false then -x else 1) + (if true then -x else 1) = carGradedLocal x := by
  simp [carGradedLocal]
  ring

/--
Consolidated CAR/CCR/Cantor-Fock package.
-/
theorem car_ccr_cantor_fock_synthesis :
    (∀ n : ℕ, Fintype.card (CARWord n) = 2 ^ n) ∧
    (∀ n K : ℕ, Fintype.card (CCRCutoffWord n K) = (K + 1) ^ n) ∧
    carAnnihilate * carAnnihilate = 0 ∧
    carCreate * carCreate = 0 ∧
    carAnnihilate * carCreate + carCreate * carAnnihilate =
      (1 : Matrix (Fin 2) (Fin 2) ℂ) ∧
    carNumber * carNumber = carNumber ∧
    carParity * carParity = (1 : Matrix (Fin 2) (Fin 2) ℂ) ∧
    (∀ x : ℂ, ccrCutoffLocal x 0 = 1) ∧
    (∀ x : ℂ, ∀ K : ℕ,
      ccrCutoffLocal x (K + 1) = ccrCutoffLocal x K + x ^ (K + 1)) ∧
    (∀ x : ℂ, x ≠ 1 → ccrFormalLocal x * carGradedLocal x = 1) ∧
    (∀ xs : List ℂ, (∀ x ∈ xs, x ≠ 1) →
      ccrFormalPartition xs * carGradedPartition xs = 1) := by
  exact ⟨carWord_card,
    ccrCutoffWord_card,
    carAnnihilate_sq,
    carCreate_sq,
    car_anticommutator,
    carNumber_idempotent,
    carParity_sq,
    ccrCutoffLocal_zero,
    ccrCutoffLocal_succ,
    fun x hx => ccrFormal_cancels_carGraded hx,
    ccrFormalPartition_cancels_carGraded⟩

end CARCCRCantorFock

end noncomputable section
