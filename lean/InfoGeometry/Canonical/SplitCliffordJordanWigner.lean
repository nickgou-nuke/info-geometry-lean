import InfoGeometry.Canonical.SplitCliffordSourceWickBase

/-!
# InfoGeometry.Canonical.SplitCliffordJordanWigner

Concrete Jordan-Wigner parity operator in `M₂(ℝ)`.

This file proves the local grading facts needed to turn tensor products of
single-mode parabolic atoms into fermionic multi-mode CAR operators:

* `P^2 = 1`;
* `P*a + a*P = 0`;
* `P*a† + a†*P = 0`;
* conjugation by `P` flips the sign of `a` and `a†`.

No wrappers. No placeholders.
-/

namespace InfoGeometry.Canonical.SplitCliffordJordanWigner

open Matrix
open InfoGeometry.Canonical.SplitCliffordSourceWickBase

/--
Local fermionic parity/grading operator:

`P = a*a† - a†*a`.

In the standard basis this is the diagonal grading matrix.
-/
def P : M2R :=
  a * aDag - aDag * a

/-- Coordinate form of the parity operator. -/
theorem P_eq_diag :
    P = !![1, 0;
           0, -1] := by
  ext i j <;> fin_cases i <;> fin_cases j <;>
    norm_num [P, a, aDag, N, Matrix.mul_apply, Fin.sum_univ_two]

/--
The parity operator squares to the identity.

This is the involution property required for Jordan-Wigner strings.
-/
@[simp]
theorem parity_sq_eq_one :
    P * P = (1 : M2R) := by
  ext i j <;> fin_cases i <;> fin_cases j <;>
    norm_num [P, a, aDag, N, Matrix.mul_apply, Fin.sum_univ_two]

/--
Parity anticommutes with the annihilation operator:

`P*a + a*P = 0`.
-/
@[simp]
theorem parity_anticommutes_annihilate :
    P * a + a * P = (0 : M2R) := by
  ext i j <;> fin_cases i <;> fin_cases j <;>
    norm_num [P, a, aDag, N, Matrix.mul_apply, Fin.sum_univ_two]

/--
Parity anticommutes with the creation operator:

`P*a† + a†*P = 0`.
-/
@[simp]
theorem parity_anticommutes_create :
    P * aDag + aDag * P = (0 : M2R) := by
  ext i j <;> fin_cases i <;> fin_cases j <;>
    norm_num [P, a, aDag, N, Matrix.mul_apply, Fin.sum_univ_two]

/--
Conjugation by parity flips annihilation:

`P*a*P = -a`.
-/
theorem parity_conj_annihilate :
    P * a * P = -a := by
  ext i j <;> fin_cases i <;> fin_cases j <;>
    norm_num [P, a, aDag, N, Matrix.mul_apply, Fin.sum_univ_two]

/--
Conjugation by parity flips creation:

`P*a†*P = -a†`.
-/
theorem parity_conj_create :
    P * aDag * P = -aDag := by
  ext i j <;> fin_cases i <;> fin_cases j <;>
    norm_num [P, a, aDag, N, Matrix.mul_apply, Fin.sum_univ_two]

/--
Parity preserves the vacuum line:

`P |0⟩ = |0⟩`.
-/
theorem parity_vacuum :
    P * vac = vac := by
  ext i j <;> fin_cases i <;> fin_cases j <;>
    norm_num [P, a, aDag, N, vac, Matrix.mul_apply, Fin.sum_univ_two]

end InfoGeometry.Canonical.SplitCliffordJordanWigner

