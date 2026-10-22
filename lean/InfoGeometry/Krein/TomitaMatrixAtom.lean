/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/

import Mathlib.Tactic
import Mathlib.Algebra.Order.Star.Real
import Mathlib.LinearAlgebra.Matrix.PosDef
import InfoGeometry.Algebra.FiniteSpinAlgebra

noncomputable section

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
open InfoGeometry.Algebra.FiniteSpin

/-- Tomita/Krein reflection: swaps the two real components. -/
def J : Mat2R :=
  !![0, 1;
     1, 0]

/-- Krein sign/chirality involution. -/
def eps : Mat2R :=
  !![1, 0;
     0, -1]

/-- Positive sector projector. -/
def Pplus : Mat2R :=
  !![1, 0;
     0, 0]

/-- Negative sector projector. -/
def Pminus : Mat2R :=
  !![0, 0;
     0, 1]

/-- Transition from negative sector to positive sector. -/
def ellPlus : Mat2R :=
  !![0, 1;
     0, 0]

/-- Transition from positive sector to negative sector. -/
def ellMinus : Mat2R :=
  !![0, 0;
     1, 0]

/-- Finite Dirac-Hodge atom: the sum of both sheet transitions. -/
def diracHodgeAtom : Mat2R :=
  ellPlus + ellMinus

@[simp]
theorem J_sq :
    J * J = (1 : Mat2R) := by
  ext i j; fin_cases i <;> fin_cases j <;>
    norm_num [J, Matrix.mul_apply, Fin.sum_univ_two]

@[simp]
theorem eps_sq :
    eps * eps = (1 : Mat2R) := by
  ext i j; fin_cases i <;> fin_cases j <;>
    norm_num [eps, Matrix.mul_apply, Fin.sum_univ_two]

/-- The Tomita reflection anticommutes with the Krein sign. -/
theorem J_mul_eps_eq_neg_eps_mul_J :
    J * eps = - (eps * J) := by
  ext i j; fin_cases i <;> fin_cases j <;>
    norm_num [J, eps, Matrix.mul_apply, Fin.sum_univ_two]

/-- The internal complex axis squares to `-1`. -/
theorem J_eps_sq :
    (J * eps) * (J * eps) = (-1 : Mat2R) := by
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
    Pplus + Pminus = (1 : Mat2R) := by
  ext i j; fin_cases i <;> fin_cases j <;>
    norm_num [Pplus, Pminus]

@[simp]
theorem Pplus_sub_Pminus :
    Pplus - Pminus = eps := by
  ext i j; fin_cases i <;> fin_cases j <;>
    norm_num [Pplus, Pminus, eps]

/-- `P₊ = (1 + ε)/2`. -/
theorem Pplus_eq_half_one_add_eps :
    Pplus = ((1 / 2 : ℝ) • ((1 : Mat2R) + eps)) := by
  ext i j; fin_cases i <;> fin_cases j <;>
    norm_num [Pplus, eps]

/-- `P₋ = (1 - ε)/2`. -/
theorem Pminus_eq_half_one_sub_eps :
    Pminus = ((1 / 2 : ℝ) • ((1 : Mat2R) - eps)) := by
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
    ellPlus * ellMinus + ellMinus * ellPlus = (1 : Mat2R) := by
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
    diracHodgeAtom * diracHodgeAtom = (1 : Mat2R) := by
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

/-! ### Finite two-sector thermal polarization

The grading stays fixed while the scalar parameter changes the weights of its
two eigensectors.  These are matrix identities in the existing `Mat2R` owner;
they do not assert positivity or a trace-class interpretation outside this
finite carrier.
-/

/-- The normalized two-sector polarization attached to a real parameter. -/
def thermalPolarization (q : ℝ) : Mat2R :=
  ((1 / 2 : ℝ) • ((1 : Mat2R) + q • eps))

/-- The scalar weights of the positive and negative sectors. -/
def thermalWeightPlus (q : ℝ) : ℝ := (1 + q) / 2

def thermalWeightMinus (q : ℝ) : ℝ := (1 - q) / 2

@[simp]
theorem thermalWeights_add (q : ℝ) :
    thermalWeightPlus q + thermalWeightMinus q = 1 := by
  unfold thermalWeightPlus thermalWeightMinus
  ring

@[simp]
theorem thermalWeights_sub (q : ℝ) :
    thermalWeightPlus q - thermalWeightMinus q = q := by
  unfold thermalWeightPlus thermalWeightMinus
  ring

/-- The thermal polarization is the weighted sum of the two projectors. -/
theorem thermalPolarization_eq_weighted_projectors (q : ℝ) :
    thermalPolarization q =
      thermalWeightPlus q • Pplus + thermalWeightMinus q • Pminus := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [thermalPolarization, thermalWeightPlus, thermalWeightMinus,
      Pplus, Pminus, eps] <;>
    ring

/-- The polarization is the affine expression `½ (1 + q ε)`. -/
theorem thermalPolarization_eq_affine (q : ℝ) :
    thermalPolarization q =
      ((1 / 2 : ℝ) • (1 : Mat2R)) + (q / 2) • eps := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [thermalPolarization, eps] <;>
    ring

/-- The finite two-sector polarization has trace one for every real contrast. -/
theorem thermalPolarization_trace (q : ℝ) :
    Matrix.trace (thermalPolarization q) = 1 := by
  rw [thermalPolarization_eq_affine]
  simp [Matrix.trace, eps]
  ring

/-- The signed expectation of the fixed Krein grading in the finite thermal
polarization is its contrast parameter. -/
theorem thermalPolarization_grading_expectation (q : ℝ) :
    Matrix.trace (thermalPolarization q * eps) = q := by
  rw [thermalPolarization_eq_affine]
  simp [Matrix.trace, Matrix.mul_apply, eps, Fin.sum_univ_two]
  ring

/-- The two-sector polarization is positive semidefinite exactly when both
sector weights are nonnegative, equivalently when its contrast lies in
`[-1, 1]`. -/
theorem thermalPolarization_posSemidef_iff (q : ℝ) :
    Matrix.PosSemidef (thermalPolarization q) ↔ -1 ≤ q ∧ q ≤ 1 := by
  have hdiag : thermalPolarization q =
      Matrix.diagonal ![(1 + q) / 2, (1 - q) / 2] := by
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [thermalPolarization, eps, Matrix.diagonal] <;>
      ring
  rw [hdiag, Matrix.posSemidef_diagonal_iff]
  constructor
  · intro h
    constructor
    · have h₀ := h 0
      norm_num at h₀
      linarith
    · have h₁ := h 1
      norm_num at h₁
      linarith
  · rintro ⟨hq_lower, hq_upper⟩ i
    fin_cases i <;> simp <;> linarith

/-- Squaring the polarization gives the exact scalar defect from idempotence. -/
theorem thermalPolarization_sq_sub_self (q : ℝ) :
    thermalPolarization q * thermalPolarization q - thermalPolarization q =
      ((q ^ 2 - 1) / 4 : ℝ) • (1 : Mat2R) := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [thermalPolarization, eps, Matrix.mul_apply, Fin.sum_univ_two]
  <;> ring

/-- At zero polarization, both sectors have equal weight. -/
theorem thermalPolarization_zero :
    thermalPolarization 0 = ((1 / 2 : ℝ) • (1 : Mat2R)) := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [thermalPolarization, eps]

/-- The two extremal parameters recover the sector projectors. -/
theorem thermalPolarization_one :
    thermalPolarization 1 = Pplus := by
  rw [thermalPolarization_eq_weighted_projectors]
  norm_num [thermalWeightPlus, thermalWeightMinus]

theorem thermalPolarization_neg_one :
    thermalPolarization (-1) = Pminus := by
  rw [thermalPolarization_eq_weighted_projectors]
  norm_num [thermalWeightPlus, thermalWeightMinus]

end InfoGeometry.Krein.TomitaMatrixAtom
