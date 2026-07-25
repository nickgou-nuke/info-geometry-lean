import Mathlib.Tactic

/-!
# InfoGeometry.Krein.TomitaMatrixAtom

Concrete `2 × 2` real Tomita/Krein atom.

This file proves the finite split-Clifford atom directly:

* `J² = 1`
* `ε² = 1`
* `J ε = - ε J`
* `P₊² = P₊`, `P₋² = P₋`
* `P₊ P₋ = 0`, `P₊ + P₋ = 1`
* `ℓ₊² = 0`, `ℓ₋² = 0`
* `ℓ₊ ℓ₋ = P₊`, `ℓ₋ ℓ₊ = P₋`
* `{ℓ₊,ℓ₋} = 1`
* `[ℓ₊,ℓ₋] = ε`
* `J ℓ₊ J = ℓ₋`, `J ℓ₋ J = ℓ₊`
* `D = ℓ₊ + J ℓ₊ J = J`
* `{D, ε} = 0`
* `D ε D = -ε`
* `D P₊ D = P₋`, `D P₋ D = P₊`
* `D P₊ = P₋ D`, `D P₋ = P₊ D`

No current algebra.
No Sugawara.
No source-completion claim.

#### BUCKET 1: CLOSED FINITE THEOREMS
All theorems in this file are concrete `2 × 2` matrix identities over `ℝ`.

#### BUCKET 2: CONDITIONAL THEOREMS FROM EXPLICIT WITNESSES
None.

#### BUCKET 3: OPEN CLOSURE DEBT
Any infinite-dimensional Tomita-Takesaki, KMS, Cuntz-algebra, spectral-triple,
or analytic Dirac-Hodge interpretation.
-/

namespace InfoGeometry.Krein.TomitaMatrixAtom

open Matrix

abbrev M2R := Matrix (Fin 2) (Fin 2) ℝ

/-- Tomita/Krein reflection: swaps the two real components. -/
def J : M2R :=
  !![0, 1;
     1, 0]

/-- Krein sign/chirality involution. -/
def eps : M2R :=
  !![1, 0;
     0, -1]

/-- Positive sector projector. -/
def Pplus : M2R :=
  !![1, 0;
     0, 0]

/-- Negative sector projector. -/
def Pminus : M2R :=
  !![0, 0;
     0, 1]

/-- Transition from negative sector to positive sector. -/
def ellPlus : M2R :=
  !![0, 1;
     0, 0]

/-- Transition from positive sector to negative sector. -/
def ellMinus : M2R :=
  !![0, 0;
     1, 0]

/-- Finite Dirac-Hodge atom: the sum of both sheet transitions. -/
def diracHodgeAtom : M2R :=
  ellPlus + ellMinus

@[simp]
theorem J_sq :
    J * J = (1 : M2R) := by
  ext i j; fin_cases i <;> fin_cases j <;>
    norm_num [J, Matrix.mul_apply, Fin.sum_univ_two]

@[simp]
theorem eps_sq :
    eps * eps = (1 : M2R) := by
  ext i j; fin_cases i <;> fin_cases j <;>
    norm_num [eps, Matrix.mul_apply, Fin.sum_univ_two]

/-- The Tomita reflection anticommutes with the Krein sign. -/
theorem J_mul_eps_eq_neg_eps_mul_J :
    J * eps = - (eps * J) := by
  ext i j; fin_cases i <;> fin_cases j <;>
    norm_num [J, eps, Matrix.mul_apply, Fin.sum_univ_two]

/-- The internal complex axis squares to `-1`. -/
theorem J_eps_sq :
    (J * eps) * (J * eps) = (-1 : M2R) := by
  ext i j; fin_cases i <;> fin_cases j <;>
    norm_num [J, eps, Matrix.mul_apply, Fin.sum_univ_two]

@[simp]
theorem Pplus_idempotent :
    Pplus * Pplus = Pplus := by
  ext i j; fin_cases i <;> fin_cases j <;>
    norm_num [Pplus, Matrix.mul_apply, Fin.sum_univ_two]

@[simp]
theorem Pminus_idempotent :
    Pminus * Pminus = Pminus := by
  ext i j; fin_cases i <;> fin_cases j <;>
    norm_num [Pminus, Matrix.mul_apply, Fin.sum_univ_two]

@[simp]
theorem Pplus_mul_Pminus :
    Pplus * Pminus = 0 := by
  ext i j; fin_cases i <;> fin_cases j <;>
    norm_num [Pplus, Pminus, Matrix.mul_apply, Fin.sum_univ_two]

@[simp]
theorem Pminus_mul_Pplus :
    Pminus * Pplus = 0 := by
  ext i j; fin_cases i <;> fin_cases j <;>
    norm_num [Pplus, Pminus, Matrix.mul_apply, Fin.sum_univ_two]

@[simp]
theorem Pplus_add_Pminus :
    Pplus + Pminus = (1 : M2R) := by
  ext i j; fin_cases i <;> fin_cases j <;>
    norm_num [Pplus, Pminus]

@[simp]
theorem Pplus_sub_Pminus :
    Pplus - Pminus = eps := by
  ext i j; fin_cases i <;> fin_cases j <;>
    norm_num [Pplus, Pminus, eps]

/-- `P₊ = (1 + ε)/2`. -/
theorem Pplus_eq_half_one_add_eps :
    Pplus = ((1 / 2 : ℝ) • ((1 : M2R) + eps)) := by
  ext i j; fin_cases i <;> fin_cases j <;>
    norm_num [Pplus, eps]

/-- `P₋ = (1 - ε)/2`. -/
theorem Pminus_eq_half_one_sub_eps :
    Pminus = ((1 / 2 : ℝ) • ((1 : M2R) - eps)) := by
  ext i j; fin_cases i <;> fin_cases j <;>
    norm_num [Pminus, eps]

/-- The upper transition is square-zero. -/
@[simp]
theorem ellPlus_square_zero :
    ellPlus * ellPlus = 0 := by
  ext i j; fin_cases i <;> fin_cases j <;>
    norm_num [ellPlus, Matrix.mul_apply, Fin.sum_univ_two]

/-- The lower transition is square-zero. -/
@[simp]
theorem ellMinus_square_zero :
    ellMinus * ellMinus = 0 := by
  ext i j; fin_cases i <;> fin_cases j <;>
    norm_num [ellMinus, Matrix.mul_apply, Fin.sum_univ_two]

/-- The upper then lower transition recovers the positive projector. -/
@[simp]
theorem ellPlus_mul_ellMinus :
    ellPlus * ellMinus = Pplus := by
  ext i j; fin_cases i <;> fin_cases j <;>
    norm_num [ellPlus, ellMinus, Pplus, Matrix.mul_apply, Fin.sum_univ_two]

/-- The lower then upper transition recovers the negative projector. -/
@[simp]
theorem ellMinus_mul_ellPlus :
    ellMinus * ellPlus = Pminus := by
  ext i j; fin_cases i <;> fin_cases j <;>
    norm_num [ellPlus, ellMinus, Pminus, Matrix.mul_apply, Fin.sum_univ_two]

/-- The transition anticommutator is the identity. -/
theorem ell_anticommutator :
    ellPlus * ellMinus + ellMinus * ellPlus = (1 : M2R) := by
  rw [ellPlus_mul_ellMinus, ellMinus_mul_ellPlus, Pplus_add_Pminus]

/-- The transition commutator is the Krein sign. -/
theorem ell_commutator :
    ellPlus * ellMinus - ellMinus * ellPlus = eps := by
  rw [ellPlus_mul_ellMinus, ellMinus_mul_ellPlus, Pplus_sub_Pminus]

/-- The upper transition is supported from `P₋` to `P₊`. -/
theorem ellPlus_support :
    Pplus * ellPlus = ellPlus ∧ ellPlus * Pminus = ellPlus := by
  constructor
  · ext i j; fin_cases i <;> fin_cases j <;>
      norm_num [Pplus, ellPlus, Matrix.mul_apply, Fin.sum_univ_two]
  · ext i j; fin_cases i <;> fin_cases j <;>
      norm_num [Pminus, ellPlus, Matrix.mul_apply, Fin.sum_univ_two]

/-- The lower transition is supported from `P₊` to `P₋`. -/
theorem ellMinus_support :
    Pminus * ellMinus = ellMinus ∧ ellMinus * Pplus = ellMinus := by
  constructor
  · ext i j; fin_cases i <;> fin_cases j <;>
      norm_num [Pminus, ellMinus, Matrix.mul_apply, Fin.sum_univ_two]
  · ext i j; fin_cases i <;> fin_cases j <;>
      norm_num [Pplus, ellMinus, Matrix.mul_apply, Fin.sum_univ_two]

/--
`ellPlus` is exactly `P₊ J P₋`.
-/
theorem ellPlus_eq_Pplus_J_Pminus :
    ellPlus = Pplus * J * Pminus := by
  ext i j; fin_cases i <;> fin_cases j <;>
    norm_num [ellPlus, Pplus, J, Pminus, Matrix.mul_apply, Fin.sum_univ_two]

/--
`ellMinus` is exactly `P₋ J P₊`.
-/
theorem ellMinus_eq_Pminus_J_Pplus :
    ellMinus = Pminus * J * Pplus := by
  ext i j; fin_cases i <;> fin_cases j <;>
    norm_num [ellMinus, Pminus, J, Pplus, Matrix.mul_apply, Fin.sum_univ_two]

/-- Tomita conjugation swaps the upper transition into the lower transition. -/
theorem J_conj_ellPlus :
    J * ellPlus * J = ellMinus := by
  ext i j; fin_cases i <;> fin_cases j <;>
    norm_num [J, ellPlus, ellMinus, Matrix.mul_apply, Fin.sum_univ_two]

/-- Tomita conjugation swaps the lower transition into the upper transition. -/
theorem J_conj_ellMinus :
    J * ellMinus * J = ellPlus := by
  ext i j; fin_cases i <;> fin_cases j <;>
    norm_num [J, ellPlus, ellMinus, Matrix.mul_apply, Fin.sum_univ_two]

/-- The finite Dirac-Hodge atom is `ℓ₊ + Jℓ₊J`. -/
theorem diracHodgeAtom_eq_ellPlus_add_J_conj_ellPlus :
    diracHodgeAtom = ellPlus + J * ellPlus * J := by
  rw [J_conj_ellPlus]
  rfl

/-- In the two-sheet atom, the Dirac-Hodge transition equals the Tomita swap. -/
theorem diracHodgeAtom_eq_J :
    diracHodgeAtom = J := by
  ext i j; fin_cases i <;> fin_cases j <;>
    norm_num [diracHodgeAtom, ellPlus, ellMinus, J]

/-- The finite Dirac-Hodge atom is an involution. -/
theorem diracHodgeAtom_sq :
    diracHodgeAtom * diracHodgeAtom = (1 : M2R) := by
  rw [diracHodgeAtom_eq_J, J_sq]

/-- The finite Dirac-Hodge atom anticommutes with the Krein sign grading. -/
theorem diracHodgeAtom_anticommutes_eps :
    diracHodgeAtom * eps + eps * diracHodgeAtom = 0 := by
  ext i j; fin_cases i <;> fin_cases j <;>
    norm_num [diracHodgeAtom, ellPlus, ellMinus, eps, Matrix.mul_apply, Fin.sum_univ_two]

/-- Dirac-Hodge conjugation reverses the Krein sign grading. -/
theorem diracHodgeAtom_conj_eps :
    diracHodgeAtom * eps * diracHodgeAtom = -eps := by
  ext i j; fin_cases i <;> fin_cases j <;>
    norm_num [diracHodgeAtom, ellPlus, ellMinus, eps, Matrix.mul_apply, Fin.sum_univ_two]

/-- Dirac-Hodge conjugation swaps the positive sector projector into the negative one. -/
theorem diracHodgeAtom_conj_Pplus :
    diracHodgeAtom * Pplus * diracHodgeAtom = Pminus := by
  ext i j; fin_cases i <;> fin_cases j <;>
    norm_num [diracHodgeAtom, ellPlus, ellMinus, Pplus, Pminus,
      Matrix.mul_apply, Fin.sum_univ_two]

/-- Dirac-Hodge conjugation swaps the negative sector projector into the positive one. -/
theorem diracHodgeAtom_conj_Pminus :
    diracHodgeAtom * Pminus * diracHodgeAtom = Pplus := by
  ext i j; fin_cases i <;> fin_cases j <;>
    norm_num [diracHodgeAtom, ellPlus, ellMinus, Pplus, Pminus,
      Matrix.mul_apply, Fin.sum_univ_two]

/-- The Dirac-Hodge atom intertwines the positive projector with the negative one. -/
theorem diracHodgeAtom_mul_Pplus :
    diracHodgeAtom * Pplus = Pminus * diracHodgeAtom := by
  ext i j; fin_cases i <;> fin_cases j <;>
    norm_num [diracHodgeAtom, ellPlus, ellMinus, Pplus, Pminus,
      Matrix.mul_apply, Fin.sum_univ_two]

/-- The Dirac-Hodge atom intertwines the negative projector with the positive one. -/
theorem diracHodgeAtom_mul_Pminus :
    diracHodgeAtom * Pminus = Pplus * diracHodgeAtom := by
  ext i j; fin_cases i <;> fin_cases j <;>
    norm_num [diracHodgeAtom, ellPlus, ellMinus, Pplus, Pminus,
      Matrix.mul_apply, Fin.sum_univ_two]

end InfoGeometry.Krein.TomitaMatrixAtom
