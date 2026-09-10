import InfoGeometry.Canonical.SplitCliffordSourceWickBase
import InfoGeometry.Algebra.FiniteSpinAlgebra

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

/-- Local concrete carrier used by this owner file. -/
abbrev M2R := InfoGeometry.Algebra.FiniteSpin.Mat2R

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
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [P, a, aDag, N, Matrix.mul_apply, Fin.sum_univ_two]

/--
The parity operator squares to the identity.

This is the involution property required for Jordan-Wigner strings.
-/
@[simp]
theorem parity_sq_eq_one :
    P * P = (1 : M2R) := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [P, a, aDag, N, Matrix.mul_apply, Fin.sum_univ_two]

/--
Parity anticommutes with the annihilation operator:

`P*a + a*P = 0`.
-/
@[simp]
theorem parity_anticommutes_annihilate :
    P * a + a * P = (0 : M2R) := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [P, a, aDag, N, Matrix.mul_apply, Fin.sum_univ_two]

/--
Parity anticommutes with the creation operator:

`P*a† + a†*P = 0`.
-/
@[simp]
theorem parity_anticommutes_create :
    P * aDag + aDag * P = (0 : M2R) := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [P, a, aDag, N, Matrix.mul_apply, Fin.sum_univ_two]

/--
Conjugation by parity flips annihilation:

`P*a*P = -a`.
-/
theorem parity_conj_annihilate :
    P * a * P = -a := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [P, a, aDag, N, Matrix.mul_apply, Fin.sum_univ_two]

/--
Conjugation by parity flips creation:

`P*a†*P = -a†`.
-/
theorem parity_conj_create :
    P * aDag * P = -aDag := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [P, a, aDag, N, Matrix.mul_apply, Fin.sum_univ_two]

/--
Parity preserves the vacuum line:

`P |0⟩ = |0⟩`.
-/
theorem parity_vacuum :
    P * vac = vac := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [P, a, aDag, N, vac, Matrix.mul_apply, Fin.sum_univ_two]

/-! ## Two-mode Jordan-Wigner cross CAR base case -/

namespace TwoMode

open Matrix

/-- Concrete `4 × 4` real matrices for two fermionic modes. -/
abbrev M4R := InfoGeometry.Algebra.FiniteSpin.Mat4R

/--
First-mode annihilation operator:

`a₁ = a ⊗ 1`.

Basis order is `(00, 01, 10, 11)`.
-/
def a1 : M4R :=
  !![0, 0, 1, 0;
     0, 0, 0, 1;
     0, 0, 0, 0;
     0, 0, 0, 0]

/--
First-mode creation operator:

`a₁† = a† ⊗ 1`.
-/
def a1Dag : M4R :=
  !![0, 0, 0, 0;
     0, 0, 0, 0;
     1, 0, 0, 0;
     0, 1, 0, 0]

/--
Second-mode annihilation operator with Jordan-Wigner parity twist:

`a₂ = P ⊗ a`.

The sign on the occupied first mode is the parity string.
-/
def a2 : M4R :=
  !![0, 1, 0, 0;
     0, 0, 0, 0;
     0, 0, 0, -1;
     0, 0, 0, 0]

/--
Second-mode creation operator with Jordan-Wigner parity twist:

`a₂† = P ⊗ a†`.
-/
def a2Dag : M4R :=
  !![0, 0, 0, 0;
     1, 0, 0, 0;
     0, 0, 0, 0;
     0, 0, -1, 0]

/--
The Jordan-Wigner twist gives cross-mode annihilation anticommutation:

`a₁ a₂ + a₂ a₁ = 0`.
-/
theorem jw_cross_annihilate_anticomm :
    a1 * a2 + a2 * a1 = 0 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [a1, a2, Matrix.mul_apply, Fin.sum_univ_four]

/--
The Jordan-Wigner twist gives the cross CAR relation:

`a₁ a₂† + a₂† a₁ = 0`.

This is the concrete two-mode base case showing that the parity string turns
separate `M₂(ℝ)` ladder blocks into fermionic, not bosonic, modes.
-/
theorem jw_cross_annihilate_create_CAR :
    a1 * a2Dag + a2Dag * a1 = 0 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [a1, a2Dag, Matrix.mul_apply, Fin.sum_univ_four]

/--
The adjoint cross CAR relation:

`a₁† a₂ + a₂ a₁† = 0`.
-/
theorem jw_cross_create_annihilate_CAR :
    a1Dag * a2 + a2 * a1Dag = 0 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [a1Dag, a2, Matrix.mul_apply, Fin.sum_univ_four]

/--
Cross-mode creation operators anticommute:

`a₁† a₂† + a₂† a₁† = 0`.
-/
theorem jw_cross_create_anticomm :
    a1Dag * a2Dag + a2Dag * a1Dag = 0 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [a1Dag, a2Dag, Matrix.mul_apply, Fin.sum_univ_four]

end TwoMode

end InfoGeometry.Canonical.SplitCliffordJordanWigner
