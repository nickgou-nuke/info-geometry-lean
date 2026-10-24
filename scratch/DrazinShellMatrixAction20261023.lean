/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.Canonical.DrazinNilpotentShellResolution
import InfoGeometry.Singular.NilpotentShellAbsorption

/-!
# Native shell actions on rows and columns

Uncompiled scratch candidate. No new shell carrier is introduced.
Recovery proves a zero test at degree m, not nonzeroness of a shell or
minimality of a supplied Drazin index. Row multiplication order is retained;
the corange column statements use the native real-matrix owner.
-/

namespace InfoGeometry.Canonical.DrazinShellMatrixActionCandidate

open Matrix

variable {n : Type*} [Fintype n] [DecidableEq n]

section VectorRecovery

variable {R : Type*} [Semiring R] {S A B : Matrix n n R}

/-- Matrix right annihilation descends to every row in the image of S. -/
theorem row_annihilation (h : S * A = 0) (v : n → R) :
    (v ᵥ* S) ᵥ* A = 0 := by
  rw [vecMul_vecMul, h, vecMul_zero]

/-- A right recovery factor makes the row zero test faithful on the image of S. -/
theorem row_zero_iff_of_recovery (h : (S * A) * B = S) (v : n → R) :
    (v ᵥ* S) ᵥ* A = 0 ↔ v ᵥ* S = 0 := by
  constructor
  · intro hz
    calc
      v ᵥ* S = ((v ᵥ* S) ᵥ* A) ᵥ* B := by
        simp only [vecMul_vecMul, ← mul_assoc, h]
      _ = 0 := by rw [hz, zero_vecMul]
  · intro hz
    rw [hz, zero_vecMul]

/-- Matrix left annihilation descends to every column in the image of S. -/
theorem column_annihilation (h : A * S = 0) (v : n → R) :
    A *ᵥ (S *ᵥ v) = 0 := by
  rw [mulVec_mulVec, h, zero_mulVec]

/-- A left recovery factor makes the column zero test faithful on the image of S. -/
theorem column_zero_iff_of_recovery (h : B * (A * S) = S) (v : n → R) :
    A *ᵥ (S *ᵥ v) = 0 ↔ S *ᵥ v = 0 := by
  constructor
  · intro hz
    calc
      S *ᵥ v = B *ᵥ (A *ᵥ (S *ᵥ v)) := by
        simp only [mulVec_mulVec, mul_assoc, h]
      _ = 0 := by rw [hz, mulVec_zero]
  · intro hz
    rw [hz, mulVec_zero]

end VectorRecovery

section Rows

open Drazin DrazinNilpotentShell

variable {R : Type*} [Ring R] [StarRing R]
variable {N a d : Matrix n n R} {M : ℕ → Matrix n n R} {k : ℕ}

/-- The native raw range-shell row is killed at degree m+1. -/
theorem shell_row_pow_succ_eq_zero (hM : PowerMPFamily N M)
    (v : n → R) (m : ℕ) :
    (v ᵥ* shellProj N M m) ᵥ* N ^ (m + 1) = 0 :=
  row_annihilation (shellProj_mul_pow_eq_zero hM (le_refl (m + 1))) v

/-- At degree m, a raw shell row is zero exactly when it was already zero. -/
theorem shell_row_pow_eq_zero_iff (hM : PowerMPFamily N M)
    (v : n → R) (m : ℕ) :
    (v ᵥ* shellProj N M m) ᵥ* N ^ m = 0 ↔ v ᵥ* shellProj N M m = 0 :=
  row_zero_iff_of_recovery (shellProj_recover hM m) v

/-- Dressed shell rows are killed by the full operator a at degree m+1. -/
theorem dressed_shell_row_pow_succ_eq_zero (h : IsDrazinInverse a d k)
    (hM : PowerMPFamily (fittingNilpotentPart a d) M) (v : n → R) (m : ℕ) :
    (v ᵥ* drazinShellProj a d M m) ᵥ* a ^ (m + 1) = 0 :=
  row_annihilation (drazinShellProj_mul_pow_succ_eq_zero h hM m) v

/-- The native dressed recovery factor gives the exact degree-m row zero test. -/
theorem dressed_shell_row_pow_eq_zero_iff (h : IsDrazinInverse a d k)
    (hM : PowerMPFamily (fittingNilpotentPart a d) M) (v : n → R) (m : ℕ) :
    (v ᵥ* drazinShellProj a d M m) ᵥ* a ^ m = 0 ↔
      v ᵥ* drazinShellProj a d M m = 0 :=
  row_zero_iff_of_recovery (drazinShellProj_not_absorbed_at_m h hM m 0).1 v

end Rows

section RealColumns

open InfoGeometry.Singular.NilpotentShellFiltration

variable {N : Matrix n n ℝ} {M : ℕ → Matrix n n ℝ}

/-- The native real corange-shell column is killed at degree m+1. -/
theorem corange_shell_column_pow_succ_eq_zero (hM : PowerMPFamily N M)
    (v : n → ℝ) (m : ℕ) :
    N ^ (m + 1) *ᵥ (corangeShell N M m *ᵥ v) = 0 :=
  column_annihilation (pow_mul_corangeShell_eq_zero hM (le_refl (m + 1))) v

/-- At degree m, a corange-shell column is zero exactly when it was already zero. -/
theorem corange_shell_column_pow_eq_zero_iff (hM : PowerMPFamily N M)
    (v : n → ℝ) (m : ℕ) :
    N ^ m *ᵥ (corangeShell N M m *ᵥ v) = 0 ↔ corangeShell N M m *ᵥ v = 0 :=
  column_zero_iff_of_recovery (corangeShell_recover hM m) v

end RealColumns

end InfoGeometry.Canonical.DrazinShellMatrixActionCandidate
