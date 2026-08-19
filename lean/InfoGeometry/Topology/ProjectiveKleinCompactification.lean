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

theorem projectivelyEqual_refl (A : M2Q) :
    ProjectivelyEqual A A := by
  exact Or.inl rfl

theorem projectivelyEqual_symm {A B : M2Q}
    (h : ProjectivelyEqual A B) :
    ProjectivelyEqual B A := by
  rcases h with h | h
  · exact Or.inl h.symm
  · right
    rw [h]
    simp

theorem projectivelyEqual_trans {A B C : M2Q}
    (hAB : ProjectivelyEqual A B)
    (hBC : ProjectivelyEqual B C) :
    ProjectivelyEqual A C := by
  rcases hAB with hAB | hAB <;> rcases hBC with hBC | hBC
  · exact Or.inl (hAB.trans hBC)
  · right
    rw [hAB, hBC]
  · right
    rw [hAB, hBC]
  · left
    rw [hAB, hBC]
    simp

/-- The central-sign quotient used by this finite projective chart. -/
def centralSignSetoid : Setoid M2Q where
  r := ProjectivelyEqual
  iseqv := {
    refl := projectivelyEqual_refl
    symm := projectivelyEqual_symm
    trans := projectivelyEqual_trans
  }

/-- Quotient carrier for the finite central-sign projective relation. -/
abbrev CentralSignQuotient := Quotient centralSignSetoid

/-- The canonical quotient map to central-sign classes. -/
def centralSignClass (A : M2Q) : CentralSignQuotient :=
  Quotient.mk centralSignSetoid A

theorem centralSignClass_eq_iff (A B : M2Q) :
    centralSignClass A = centralSignClass B ↔ ProjectivelyEqual A B := by
  exact Quotient.eq

theorem projectivelyEqual_mul {A A' B B' : M2Q}
    (hA : ProjectivelyEqual A A')
    (hB : ProjectivelyEqual B B') :
    ProjectivelyEqual (A * B) (A' * B') := by
  rcases hA with hA | hA <;> rcases hB with hB | hB
  · exact Or.inl (congrArg₂ (· * ·) hA hB)
  · right
    rw [hA, hB]
    simp
  · right
    rw [hA, hB]
    simp
  · left
    rw [hA, hB]
    simp

/-- Multiplication on central-sign classes induced by matrix multiplication. -/
def centralSignMul (x y : CentralSignQuotient) : CentralSignQuotient :=
  Quotient.liftOn₂ x y
    (fun A B => centralSignClass (A * B))
    (by
      intro A B A' B' hA hB
      change ProjectivelyEqual A A' at hA
      change ProjectivelyEqual B B' at hB
      exact (centralSignClass_eq_iff (A * B) (A' * B')).2
        (projectivelyEqual_mul hA hB))

theorem centralSignMul_mk (A B : M2Q) :
    centralSignMul (centralSignClass A) (centralSignClass B) =
      centralSignClass (A * B) := by
  rfl

theorem centralSignMul_assoc (x y z : CentralSignQuotient) :
    centralSignMul (centralSignMul x y) z =
      centralSignMul x (centralSignMul y z) := by
  induction x using Quotient.inductionOn with
  | _ A =>
    induction y using Quotient.inductionOn with
    | _ B =>
    induction z using Quotient.inductionOn with
    | _ C =>
        change centralSignMul
          (centralSignMul (centralSignClass A) (centralSignClass B))
          (centralSignClass C) =
          centralSignMul (centralSignClass A)
            (centralSignMul (centralSignClass B) (centralSignClass C))
        rw [centralSignMul_mk, centralSignMul_mk,
          centralSignMul_mk, centralSignMul_mk, mul_assoc]

def centralSignOne : CentralSignQuotient :=
  centralSignClass (1 : M2Q)

theorem centralSignMul_one (x : CentralSignQuotient) :
    centralSignMul x centralSignOne = x := by
  induction x using Quotient.inductionOn with
  | _ A =>
    change centralSignMul (centralSignClass A)
      (centralSignClass (1 : M2Q)) = centralSignClass A
    rw [centralSignMul_mk]
    simp

theorem centralSignOne_mul (x : CentralSignQuotient) :
    centralSignMul centralSignOne x = x := by
  induction x using Quotient.inductionOn with
  | _ A =>
    change centralSignMul (centralSignClass (1 : M2Q))
      (centralSignClass A) = centralSignClass A
    rw [centralSignMul_mk]
    simp

instance : Monoid CentralSignQuotient where
  mul := centralSignMul
  one := centralSignOne
  mul_assoc := centralSignMul_assoc
  one_mul := centralSignOne_mul
  mul_one := centralSignMul_one

/-- The canonical multiplicative projection to central-sign classes. -/
def centralSignClassHom : M2Q →* CentralSignQuotient where
  toFun := centralSignClass
  map_one' := rfl
  map_mul' A B := (centralSignMul_mk A B).symm

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

end InfoGeometry.Topology.ProjectiveKleinCompactification

end noncomputable section
