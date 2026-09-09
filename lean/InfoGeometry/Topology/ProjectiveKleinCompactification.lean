import Mathlib.Tactic

/-!
# Projective Klein Compactification

Finite algebraic core for the "it is not the sphere, it is the bottle" picture.
The module keeps only the formula-level statements that can be checked by the
Lean kernel over exact rational `2 x 2` matrices.

#### BUCKET 1: CLOSED FINITE THEOREMS
* The projective sign relation identifies `I` and `-I`.
* The orientation-reversing generator conjugates the parabolic translation to
  its inverse.
* The Klein bottle presentation relation `a * b * a^{-1} * b = I` holds.
* The Mobius inversion matrix sends `[t, 1]` to `[-1, t]`.

#### BUCKET 2: CONDITIONAL THEOREMS FROM EXPLICIT PREMISES
None.

#### BUCKET 3: OPEN CLOSURE DEBT
This file does not prove analytic compactness, Painleve isomonodromy,
classification of Klein-bottle homogeneous spaces, or a diffeomorphism theorem.
-/

noncomputable section

namespace InfoGeometry.Topology.ProjectiveKleinCompactification

abbrev M2Q := Matrix (Fin 2) (Fin 2) ℚ

/-- Projective equality modulo the central sign `{I, -I}`. -/
def ProjectivelyEqual (A B : M2Q) : Prop :=
  A = B ∨ A = -B

/-- Identity matrix in the finite projective chart. -/
def I2 : M2Q := 1

/-- The nontrivial central sign. -/
def minusI2 : M2Q := -1

/-- Orientation-reversing generator for the Klein-bottle chart. -/
def twistA : M2Q :=
  !![1, 0;
     0, -1]

/-- Parabolic translation generator. -/
def parabolicB : M2Q :=
  !![1, 1;
     0, 1]

/-- Inverse parabolic translation. -/
def parabolicBInv : M2Q :=
  !![1, -1;
     0, 1]

/-- Mobius inversion/refocusing generator. -/
def mobiusS : M2Q :=
  !![0, -1;
     1, 0]

/-- The projective centralizer identifies `I` and `-I`. -/
theorem projective_identifies_central_sign :
    ProjectivelyEqual I2 minusI2 := by
  right
  ext i j
  fin_cases i <;> fin_cases j <;> norm_num [I2, minusI2]

/-- The nontrivial central sign squares to the identity. -/
theorem central_sign_square :
    minusI2 * minusI2 = I2 := by
  ext i j; fin_cases i <;> fin_cases j <;> norm_num [minusI2, I2]

/-- The twist generator is its own inverse. -/
theorem twistA_square :
    twistA * twistA = I2 := by
  ext i j; fin_cases i <;> fin_cases j <;> norm_num [twistA, I2]

/-- The parabolic inverse is exact. -/
theorem parabolicB_mul_inv :
    parabolicB * parabolicBInv = I2 := by
  ext i j; fin_cases i <;> fin_cases j <;> norm_num [parabolicB, parabolicBInv, I2]

/-- The inverse parabolic is exact on the other side as well. -/
theorem parabolicB_inv_mul :
    parabolicBInv * parabolicB = I2 := by
  ext i j; fin_cases i <;> fin_cases j <;> norm_num [parabolicB, parabolicBInv, I2]

/--
The orientation-reversing loop conjugates the parabolic translation into its
inverse. This is the finite algebraic form of the Klein-bottle glide twist.
-/
theorem twist_conjugates_parabolic :
    twistA * parabolicB * twistA = parabolicBInv := by
  ext i j; fin_cases i <;> fin_cases j <;> norm_num [twistA, parabolicB, parabolicBInv]

/-- Klein bottle presentation relation `a b a^{-1} b = I`, using `a^{-1}=a`. -/
theorem klein_bottle_relation :
    twistA * parabolicB * twistA * parabolicB = I2 := by
  ext i j; fin_cases i <;> fin_cases j <;> norm_num [twistA, parabolicB, I2]

/-- The two order-two central signs are projectively equal. -/
theorem projective_relation_respects_central_square :
    ProjectivelyEqual (minusI2 * minusI2) I2 := by
  left
  exact central_sign_square

/-- Mobius inversion sends the affine vector `[t, 1]` to `[-1, t]`. -/
theorem mobius_refocus_vector (t : ℚ) :
    mobiusS.mulVec ![t, 1] = ![-1, t] := by
  ext i
  fin_cases i <;> norm_num [mobiusS, Matrix.mulVec, Fin.sum_univ_two]

/-- The inversion square is the central negative sign, hence projectively trivial. -/
theorem mobius_square_projectively_identity :
    ProjectivelyEqual (mobiusS * mobiusS) I2 := by
  right
  ext i j; fin_cases i <;> fin_cases j <;> norm_num [mobiusS, I2]

/-! The projective chart also has an honest order-four lift before passing to
the central-sign quotient.  This is the finite algebraic content of a
cyclotomic glide; no Pin interpretation is needed for the statement. -/

theorem mobius_square_eq_minusI :
    mobiusS * mobiusS = minusI2 := by
  ext i j
  fin_cases i <;> fin_cases j <;> norm_num [mobiusS, minusI2]

theorem mobius_fourth_power :
    mobiusS ^ 4 = I2 := by
  calc
    mobiusS ^ 4 = (mobiusS * mobiusS) * (mobiusS * mobiusS) := by noncomm_ring
    _ = minusI2 * minusI2 := by rw [mobius_square_eq_minusI]
    _ = I2 := central_sign_square

end InfoGeometry.Topology.ProjectiveKleinCompactification

end noncomputable section
