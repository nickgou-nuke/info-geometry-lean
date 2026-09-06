import Mathlib

/-!
# InfoGeometry.Canonical.SplitCliffordJordanWignerTwoModeCurrent

Finite two-mode current table from the Jordan--Wigner CAR matrices.

This file proves concrete current identities in `M₄(ℝ)`.

No wrappers.
No abstract witness.
No Sugawara.
No `sorry`.
-/

namespace InfoGeometry.Canonical.SplitCliffordJordanWignerTwoModeCurrent

open Matrix
open Filter

abbrev M4R := Matrix (Fin 4) (Fin 4) ℝ

/-- First annihilation mode: `a₁ = a ⊗ I`. -/
def a1 : M4R :=
  !![0, 0, 1, 0;
     0, 0, 0, 1;
     0, 0, 0, 0;
     0, 0, 0, 0]

/-- First creation mode: `a₁† = a† ⊗ I`. -/
def a1Dag : M4R :=
  !![0, 0, 0, 0;
     0, 0, 0, 0;
     1, 0, 0, 0;
     0, 1, 0, 0]

/-- Second annihilation mode with Jordan--Wigner twist: `a₂ = P ⊗ a`. -/
def a2 : M4R :=
  !![0, 1, 0, 0;
     0, 0, 0, 0;
     0, 0, 0, -1;
     0, 0, 0, 0]

/-- Second creation mode with Jordan--Wigner twist: `a₂† = P ⊗ a†`. -/
def a2Dag : M4R :=
  !![0, 0, 0, 0;
     1, 0, 0, 0;
     0, 0, 0, 0;
     0, 0, -1, 0]

/-- Finite current `J₁ = a₁† a₂`. -/
def Jplus : M4R :=
  a1Dag * a2

/-- Finite current `J₋₁ = a₂† a₁`. -/
def Jminus : M4R :=
  a2Dag * a1

/-- Explicit commutator matrix `[J₁,J₋₁]`. -/
def Hdiag : M4R :=
  !![0, 0, 0, 0;
     0, -1, 0, 0;
     0, 0, 1, 0;
     0, 0, 0, 0]

/-- Matrix commutator. -/
def commM4 (X Y : M4R) : M4R :=
  X * Y - Y * X

/--
Finite current mode family.

Only modes `1` and `-1` are supported.
-/
def Jfin (n : Int) : M4R :=
  if n = 1 then Jplus
  else if n = (-1 : Int) then Jminus
  else 0

@[simp]
theorem Jfin_eval_one :
    Jfin 1 = Jplus := by
  simp [Jfin]

@[simp]
theorem Jfin_eval_neg_one :
    Jfin (-1 : Int) = Jminus := by
  simp [Jfin]

theorem Jplus_ne_zero :
    Jplus ≠ 0 := by
  intro h
  have hentry : (Jplus : M4R) (2 : Fin 4) (1 : Fin 4) = 0 := by
    simpa [h] using congrArg (fun A : M4R => A (2 : Fin 4) (1 : Fin 4)) h
  have h10 : (1 : ℝ) = 0 := by
    simpa [Jplus, a1Dag, a2, Matrix.mul_apply, Fin.sum_univ_four] using hentry
  exact one_ne_zero h10

theorem Jminus_ne_zero :
    Jminus ≠ 0 := by
  intro h
  have hentry : (Jminus : M4R) (1 : Fin 4) (2 : Fin 4) = 0 := by
    simpa [h] using congrArg (fun A : M4R => A (1 : Fin 4) (2 : Fin 4)) h
  have h10 : (1 : ℝ) = 0 := by
    simpa [Jminus, a2Dag, a1, Matrix.mul_apply, Fin.sum_univ_four] using hentry
  exact one_ne_zero h10

theorem Jfin_eq_zero_of_ne_one_ne_neg_one
    {n : Int} (h1 : n ≠ 1) (hm1 : n ≠ (-1 : Int)) :
    Jfin n = 0 := by
  simp [Jfin, h1, hm1]

/--
Exact support of the finite current family.
-/
theorem Jfin_eq_zero_iff (n : Int) :
    Jfin n = 0 ↔ n ≠ 1 ∧ n ≠ (-1 : Int) := by
  constructor
  · intro h
    constructor
    · intro hn
      rw [hn, Jfin_eval_one] at h
      exact Jplus_ne_zero h
    · intro hn
      rw [hn, Jfin_eval_neg_one] at h
      exact Jminus_ne_zero h
  · rintro ⟨h1, hm1⟩
    exact Jfin_eq_zero_of_ne_one_ne_neg_one h1 hm1

/--
Exact support of the finite current family.

`Jfin n = 0` precisely outside `{1,-1}`.
-/
theorem Jfin_support (n : Int) :
    Jfin n = 0 ↔ n ≠ 1 ∧ n ≠ (-1 : Int) :=
  Jfin_eq_zero_iff n

@[simp]
theorem Jplus_square_zero :
    Jplus * Jplus = 0 := by
  ext i j
  fin_cases i <;> fin_cases j
  all_goals
    simp [Jplus, a1Dag, a2, Matrix.mul_apply, Fin.sum_univ_four]

@[simp]
theorem Jminus_square_zero :
    Jminus * Jminus = 0 := by
  ext i j
  fin_cases i <;> fin_cases j
  all_goals
    simp [Jminus, a2Dag, a1, Matrix.mul_apply, Fin.sum_univ_four]

/-- `[J₁,J₁]=0`. -/
theorem Jfin_comm_1_1 :
    commM4 (Jfin 1) (Jfin 1) = 0 := by
  simp [commM4]

/-- `[J₋₁,J₋₁]=0`. -/
theorem Jfin_comm_neg1_neg1 :
    commM4 (Jfin (-1 : Int)) (Jfin (-1 : Int)) = 0 := by
  simp [commM4]

/-- Explicit diagonal commutator `[J₁,J₋₁]`. -/
theorem Jfin_comm_1_neg1_explicit :
    commM4 (Jfin 1) (Jfin (-1 : Int)) = Hdiag := by
  ext i j <;> fin_cases i <;> fin_cases j <;>
    norm_num
      [commM4, Jfin, Jplus, Jminus, Hdiag,
       a1, a1Dag, a2, a2Dag,
       Matrix.mul_apply, Fin.sum_univ_four]

/-- Explicit diagonal commutator `[J₋₁,J₁] = -Hdiag`. -/
theorem Jfin_comm_neg1_1_explicit :
    commM4 (Jfin (-1 : Int)) (Jfin 1) = -Hdiag := by
  ext i j <;> fin_cases i <;> fin_cases j <;>
    norm_num
      [commM4, Jfin, Jplus, Jminus, Hdiag,
       a1, a1Dag, a2, a2Dag,
       Matrix.mul_apply, Fin.sum_univ_four]

/--
If either current mode is outside the finite support `{1,-1}`, then the
commutator is zero.
-/
theorem Jfin_comm_m_n_zero_of_outside_support
    {m n : Int}
    (h :
      (m ≠ 1 ∧ m ≠ (-1 : Int)) ∨
      (n ≠ 1 ∧ n ≠ (-1 : Int))) :
    commM4 (Jfin m) (Jfin n) = 0 := by
  rcases h with hm | hn
  · have hm0 : Jfin m = 0 := (Jfin_eq_zero_iff m).2 hm
    simp [commM4, hm0]
  · have hn0 : Jfin n = 0 := (Jfin_eq_zero_iff n).2 hn
    simp [commM4, hn0]

/--
The finite current family is locally truncated on every vector.

Here vectors are represented as `4 × 1` real matrices.
-/
theorem Jfin_trunc_vector
    (v : Matrix (Fin 4) (Fin 1) ℝ) :
    ∀ᶠ l : Int in atTop, Jfin l * v = 0 := by
  refine eventually_atTop.2 ⟨(2 : Int), ?_⟩
  intro l hl
  have h1 : l ≠ 1 := by omega
  have hm1 : l ≠ (-1 : Int) := by omega
  rw [Jfin_eq_zero_of_ne_one_ne_neg_one h1 hm1]
  simp

/--
Uniform eventual zero on each matrix coefficient.
-/
theorem Jfin_trunc_uniform_matrix_entry
    (i j : Fin 4) :
    ∀ᶠ l : Int in atTop, (Jfin l) i j = 0 := by
  refine eventually_atTop.2 ⟨(2 : Int), ?_⟩
  intro l hl
  have h1 : l ≠ 1 := by omega
  have hm1 : l ≠ (-1 : Int) := by omega
  rw [Jfin_eq_zero_of_ne_one_ne_neg_one h1 hm1]
  simp

/--
Finite current commutator profile.

This is not the full affine Heisenberg law. It is the exact two-mode table:
only the pair `(1,-1)` and its reverse have a nonzero commutator.
-/
theorem Jfin_commutator_table :
    commM4 (Jfin 1) (Jfin 1) = 0 ∧
    commM4 (Jfin (-1 : Int)) (Jfin (-1 : Int)) = 0 ∧
    commM4 (Jfin 1) (Jfin (-1 : Int)) = Hdiag ∧
    commM4 (Jfin (-1 : Int)) (Jfin 1) = -Hdiag := by
  exact
    ⟨Jfin_comm_1_1,
     Jfin_comm_neg1_neg1,
     Jfin_comm_1_neg1_explicit,
     Jfin_comm_neg1_1_explicit⟩

/--
Owner-side SUSY scaling identity on the concrete two-mode current core:
`[Hdiag, Jplus] = 2 • Jplus`.
-/
theorem Hdiag_comm_Jplus :
    commM4 Hdiag Jplus = (2 : ℝ) • Jplus := by
  ext i j <;> fin_cases i <;> fin_cases j <;>
    norm_num
      [commM4, Hdiag, Jplus, a1, a1Dag, a2, a2Dag,
       Matrix.mul_apply, Fin.sum_univ_four]

/--
Owner-side SUSY scaling identity on the concrete two-mode current core:
`[Hdiag, Jminus] = -2 • Jminus`.
-/
theorem Hdiag_comm_Jminus :
    commM4 Hdiag Jminus = (-2 : ℝ) • Jminus := by
  ext i j <;> fin_cases i <;> fin_cases j <;>
    norm_num
      [commM4, Hdiag, Jminus, a1, a1Dag, a2, a2Dag,
       Matrix.mul_apply, Fin.sum_univ_four]

end InfoGeometry.Canonical.SplitCliffordJordanWignerTwoModeCurrent
