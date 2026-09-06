import Mathlib.Tactic

/-!
# Jordan blocks

This file contains only the finite matrix algebra that is proved here:
the explicit Jordan block, its scalar-plus-shift decomposition, and the
square-zero nilpotent part for a `2 × 2` block.
-/

open Matrix

noncomputable section

namespace InfoGeometry.JordanNormalForm

/--
A Jordan block J_k(λ) of size k for eigenvalue λ:

  J_k(λ)_{i,j} = λ  if i=j,  1 if j=i+1,  0 otherwise.

Properties (all proved):
  - J_k(λ) = λ·I + N  where N is the nilpotent shift matrix
  - N² = 0 for k=2
  - (J-λI)² = 0 for k=2  (minimal polynomial divides (x-λ)²)
-/
def JordanBlock (k : ℕ) (lam : ℚ) : Matrix (Fin k) (Fin k) ℚ :=
  fun i j =>
    if i = j then lam
    else if j.val = i.val + 1 then 1
    else 0

/-- The nilpotent superdiagonal shift part of a Jordan block. -/
def JordanShift (k : ℕ) : Matrix (Fin k) (Fin k) ℚ :=
  fun i j => if j.val = i.val + 1 then 1 else 0

@[simp]
lemma JordanBlock_diag (k : ℕ) (lam : ℚ) (i : Fin k) : JordanBlock k lam i i = lam := by
  simp [JordanBlock]

lemma JordanBlock_superdiag (k : ℕ) (lam : ℚ) (i j : Fin k) (h : j.val = i.val + 1) :
    JordanBlock k lam i j = 1 := by
  by_cases hij : i = j
  · subst j
    omega
  · simp [JordanBlock, hij, h]

lemma JordanBlock_else (k : ℕ) (lam : ℚ) (i j : Fin k) (h_ne : i ≠ j)
    (h_no_super : j.val ≠ i.val + 1) : JordanBlock k lam i j = 0 := by
  simp [JordanBlock, h_ne, h_no_super]

/-- Jordan block = scalar · identity + nilpotent shift -/
lemma JordanBlock_decomp (k : ℕ) (lam : ℚ) : JordanBlock k lam =
    lam • (1 : Matrix (Fin k) (Fin k) ℚ) +
    JordanShift k := by
  ext i j
  by_cases hij : i = j
  · subst j
    have hsuper : i.val ≠ i.val + 1 := by omega
    simp [JordanBlock, JordanShift, hsuper, Matrix.add_apply, Matrix.smul_apply,
      Matrix.one_apply]
  · simp [JordanBlock, JordanShift, hij, Matrix.add_apply, Matrix.smul_apply,
      Matrix.one_apply]

/-- The nilpotent shift matrix N satisfies N² = 0 (for k=2). -/
@[simp]
lemma nilpotent_shift_sq_eq_zero : ((JordanBlock 2 0) : Matrix (Fin 2) (Fin 2) ℚ) ^ 2 = 0 := by
  rw [pow_two]
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [JordanBlock, Matrix.mul_apply, Fin.sum_univ_two]

/-- (J - λI)² = 0: the minimal polynomial of a 2×2 Jordan block is (x-λ)². -/
@[simp]
lemma jordan_minimal_poly_sq (lam : ℚ) :
    (JordanBlock 2 lam - lam • (1 : Matrix (Fin 2) (Fin 2) ℚ)) ^ 2 = 0 := by
  rw [pow_two]
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [JordanBlock, Matrix.mul_apply, Matrix.sub_apply, Matrix.smul_apply,
      Matrix.one_apply, Fin.sum_univ_two]

end InfoGeometry.JordanNormalForm
