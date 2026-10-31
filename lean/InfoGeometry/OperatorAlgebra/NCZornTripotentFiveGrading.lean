/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.Canonical.OperatorZornCoefficientNucleus
import InfoGeometry.Canonical.NCZornAlternativityAudit
import InfoGeometry.OperatorAlgebra.PeirceSpine.BlockCharges
import InfoGeometry.OperatorAlgebra.PeirceSpine.EndomorphismCharge

/-!
# Noncommutative Operator Zorn Tripotent 5-Grading and Associator Defect Closure

Over an arbitrary associative coefficient ring `[Ring A]`, possibly noncommutative—without any
scalar field (`ℝ` or `ℂ`) and without dividing by `2`—the additive group of the
operator-valued Zorn carrier `OperatorZornMatrix A` (`NCZornElement A`) carries an
associative integer-linear endomorphism ring `Module.End ℤ (OperatorZornMatrix A)`.

This file establishes the characteristic-free operator algebra of `OperatorZornMatrix A`:

1. **Left and right Zorn multiplication endomorphisms (`ncZornLeftMul`, `ncZornRightMul`)**:
   Every operator Zorn element `X : OperatorZornMatrix A` acts by `ℤ`-linear left and
   right multiplication in `Module.End ℤ (OperatorZornMatrix A)`, with the unit
   `zornOne = diagonalCoefficient 1` acting as the identity endomorphism `1`.
2. **Noncommutative operator associator defect (`ncZornMulDefect`)**:
   The composition defect `ncZornMulDefect X Y := ncZornLeftMul (X * Y) - ncZornLeftMul X * ncZornLeftMul Y`
   evaluates pointwise to `associator X Y Z`, annihilates `zornOne`, and therefore lies
   outside `LinearMap.range ncZornLeftMulHom` whenever it is nonzero (in particular for
   any noncommuting coefficient witness `(a * b - b * a) * d ≠ 0`).
3. **Characteristic-free tripotent `ncZornTripotent` and 3-projection / 9-block / 5-grade
   decomposition**:
   Using the chiral sheet idempotents `ePlus = nPlus 1` and `eMinus = nMinus 1`, the
   three orthogonal projections `ncZornProj 0` (`Π₋₁`), `ncZornProj 1` (`Π₀`), and
   `ncZornProj 2` (`Π₊₁`) sum to `1` without dividing by `2`. The difference
   `ncZornTripotent := ncZornLeftMul ePlus - ncZornRightMul ePlus = Π₊₁ - Π₋₁`
   satisfies `τ³ = τ`, decomposes `Module.End ℤ (OperatorZornMatrix A)` into 9 Peirce
   blocks and 5 integer-charge sectors `(-2, -1, 0, +1, +2)`, and satisfies the universal
   quintic commutator annihilator `(ad τ)⁵ - 5 (ad τ)³ + 4 (ad τ) = 0`.
4. **Explicit 5-grade decomposition of left multiplication `ncZornLeftMul X`**:
   Grades `-1, 0, +1` of `ncZornLeftMul X` carry the `2 × 2` Peirce matrix actions of
   `(n_plus, n_minus, sigma_plus, sigma_minus)`, while the extreme grades `-2` and `+2`
   isolate the Zorn cross-product actions `zornCross X.sigma_plus` and
   `-zornCross X.sigma_minus`.
-/

namespace InfoGeometry.OperatorAlgebra.NCZornTripotentFiveGrading

open InfoGeometry.Physics.NCG
open InfoGeometry.Canonical
open InfoGeometry.Canonical.OperatorZornFourPotentialGauge
open InfoGeometry.Canonical.OperatorZornRealModule
open InfoGeometry.Canonical.OperatorZornCoefficientNucleus
open InfoGeometry.Canonical.NCZorn
open InfoGeometry.OperatorAlgebra
open InfoGeometry.OperatorAlgebra.PeirceSpine
open scoped BigOperators Matrix

variable {A : Type*} [Ring A]

/-! ## 1. Bilinearity and Unit Laws over an Arbitrary Noncommutative Ring `[Ring A]` -/

/-- The multiplicative identity element `(1, 1, 0, 0)` of `OperatorZornMatrix A`. -/
def zornOne : OperatorZornMatrix A :=
  diagonalCoefficient (1 : A)

@[simp] theorem zornOne_mul (X : OperatorZornMatrix A) :
    zornOne * X = X :=
  diagonalCoefficient_one_mul X

@[simp] theorem mul_zornOne (X : OperatorZornMatrix A) :
    X * zornOne = X :=
  mul_diagonalCoefficient_one X

theorem ncZorn_mul_add (X Y Z : OperatorZornMatrix A) :
    X * (Y + Z) = X * Y + X * Z :=
  zorn_mul_add_right X Y Z

theorem ncZorn_add_mul (X Y Z : OperatorZornMatrix A) :
    (X + Y) * Z = X * Z + Y * Z :=
  zorn_mul_add_left X Y Z

@[simp] theorem ncZorn_mul_zero (X : OperatorZornMatrix A) :
    X * (0 : OperatorZornMatrix A) = 0 := by
  apply operatorZornMatrix_ext
  · simp
  · simp
  · funext i; fin_cases i <;> simp
  · funext i; fin_cases i <;> simp

@[simp] theorem ncZorn_zero_mul (X : OperatorZornMatrix A) :
    (0 : OperatorZornMatrix A) * X = 0 := by
  apply operatorZornMatrix_ext
  · simp
  · simp
  · funext i; fin_cases i <;> simp
  · funext i; fin_cases i <;> simp

/-! ## 2. Left/Right Multiplication Endomorphisms and Associator Defect Closure -/

/-- Left multiplication by `X : OperatorZornMatrix A` as a `ℤ`-linear endomorphism. -/
def ncZornLeftMul (X : OperatorZornMatrix A) : Module.End ℤ (OperatorZornMatrix A) :=
  (AddMonoidHom.mk' (fun Y => X * Y) (ncZorn_mul_add X)).toIntLinearMap

/-- Right multiplication by `X : OperatorZornMatrix A` as a `ℤ`-linear endomorphism. -/
def ncZornRightMul (X : OperatorZornMatrix A) : Module.End ℤ (OperatorZornMatrix A) :=
  (AddMonoidHom.mk' (fun Y => Y * X) (fun Y Z => ncZorn_add_mul Y Z X)).toIntLinearMap

@[simp] theorem ncZornLeftMul_apply (X Y : OperatorZornMatrix A) :
    ncZornLeftMul X Y = X * Y := rfl

@[simp] theorem ncZornRightMul_apply (X Y : OperatorZornMatrix A) :
    ncZornRightMul X Y = Y * X := rfl

/-- Bundled `ℤ`-linear left-multiplication representation map. -/
def ncZornLeftMulHom : OperatorZornMatrix A →ₗ[ℤ] Module.End ℤ (OperatorZornMatrix A) :=
  (AddMonoidHom.mk' ncZornLeftMul (fun X Y =>
    LinearMap.ext fun Z => ncZorn_add_mul X Y Z)).toIntLinearMap

/-- Bundled `ℤ`-linear right-multiplication representation map. -/
def ncZornRightMulHom : OperatorZornMatrix A →ₗ[ℤ] Module.End ℤ (OperatorZornMatrix A) :=
  (AddMonoidHom.mk' ncZornRightMul (fun X Y =>
    LinearMap.ext fun Z => ncZorn_mul_add Z X Y)).toIntLinearMap

@[simp] theorem ncZornLeftMulHom_apply (X : OperatorZornMatrix A) :
    ncZornLeftMulHom X = ncZornLeftMul X := rfl

@[simp] theorem ncZornRightMulHom_apply (X : OperatorZornMatrix A) :
    ncZornRightMulHom X = ncZornRightMul X := rfl

@[simp] theorem ncZornLeftMul_zornOne :
    ncZornLeftMul (zornOne (A := A)) = 1 :=
  LinearMap.ext fun X => zornOne_mul X

@[simp] theorem ncZornRightMul_zornOne :
    ncZornRightMul (zornOne (A := A)) = 1 :=
  LinearMap.ext fun X => mul_zornOne X

@[simp] theorem ncZornLeftMul_apply_zornOne (X : OperatorZornMatrix A) :
    ncZornLeftMul X zornOne = X :=
  mul_zornOne X

@[simp] theorem ncZornRightMul_apply_zornOne (X : OperatorZornMatrix A) :
    ncZornRightMul X zornOne = X :=
  zornOne_mul X

theorem ncZornLeftMul_injective :
    Function.Injective (ncZornLeftMul (A := A)) := by
  intro X Y h
  have h1 := congrArg (fun K : Module.End ℤ (OperatorZornMatrix A) => K zornOne) h
  simpa only [ncZornLeftMul_apply_zornOne] using h1

/-- The noncommutative operator associator defect `L_{X * Y} - L_X ∘ L_Y` in
`Module.End ℤ (OperatorZornMatrix A)`. -/
def ncZornMulDefect (X Y : OperatorZornMatrix A) : Module.End ℤ (OperatorZornMatrix A) :=
  ncZornLeftMul (X * Y) - ncZornLeftMul X * ncZornLeftMul Y

@[simp] theorem ncZornMulDefect_apply (X Y Z : OperatorZornMatrix A) :
    ncZornMulDefect X Y Z = associator X Y Z := rfl

/-- Every multiplication-composition defect annihilates the multiplicative identity `zornOne`. -/
@[simp] theorem ncZornMulDefect_apply_zornOne (X Y : OperatorZornMatrix A) :
    ncZornMulDefect X Y zornOne = 0 := by
  simp [ncZornMulDefect]

/-- Any operator in the image of `ncZornLeftMulHom` is uniquely determined by its value on `zornOne`. -/
theorem eq_zero_of_mem_range_ncZornLeftMulHom_of_apply_zornOne
    {K : Module.End ℤ (OperatorZornMatrix A)}
    (hK : K ∈ LinearMap.range (ncZornLeftMulHom (A := A)))
    (h1 : K zornOne = 0) : K = 0 := by
  rcases hK with ⟨X, rfl⟩
  have hX : X = 0 := by
    simpa only [ncZornLeftMulHom_apply, ncZornLeftMul_apply_zornOne] using h1
  rw [hX, map_zero]

/-- A multiplication defect lies in the range of left multiplications if and only if it is zero. -/
theorem ncZornMulDefect_mem_range_iff_eq_zero (X Y : OperatorZornMatrix A) :
    ncZornMulDefect X Y ∈ LinearMap.range (ncZornLeftMulHom (A := A)) ↔
      ncZornMulDefect X Y = 0 := by
  constructor
  · intro hMem
    exact eq_zero_of_mem_range_ncZornLeftMulHom_of_apply_zornOne
      hMem (ncZornMulDefect_apply_zornOne X Y)
  · intro hZero
    rw [hZero]
    exact Submodule.zero_mem _

/-- Any nonvanishing associator forces the operator defect `ncZornMulDefect X Y` outside the
space of left multiplications. -/
theorem ncZornMulDefect_not_mem_range_of_associator_ne_zero
    {X Y Z : OperatorZornMatrix A} (hAss : associator X Y Z ≠ 0) :
    ncZornMulDefect X Y ∉ LinearMap.range (ncZornLeftMulHom (A := A)) := by
  rw [ncZornMulDefect_mem_range_iff_eq_zero]
  intro hZero
  apply hAss
  have hEval := congrArg (fun K : Module.End ℤ (OperatorZornMatrix A) => K Z) hZero
  simpa only [ncZornMulDefect_apply, LinearMap.zero_apply] using hEval

/-- Noncommuting coefficients `(a * b - b * a) * d ≠ 0` produce a concrete left-alternativity
operator defect `ncZornMulDefect (upperTwo a b) (upperTwo a b)` outside `range ncZornLeftMulHom`. -/
theorem ncZornMulDefect_upperTwo_not_mem_range
    {a b d : A} (h : (a * b - b * a) * d ≠ 0) :
    (ncZornMulDefect (upperTwo a b) (upperTwo a b) (NCZornElement.pureNPlus d)).sigma_minus 2 =
      (a * b - b * a) * d ∧
    ncZornMulDefect (upperTwo a b) (upperTwo a b) ∉
      LinearMap.range (ncZornLeftMulHom (A := A)) := by
  have hCoord :
      (ncZornMulDefect (upperTwo a b) (upperTwo a b) (NCZornElement.pureNPlus d)).sigma_minus 2 =
        (a * b - b * a) * d := by
    rw [ncZornMulDefect_apply, associator, zornSub_sigmaMinus_apply]
    change (NCZornElement.mul (NCZornElement.mul (upperTwo a b) (upperTwo a b))
        (NCZornElement.pureNPlus d)).sigma_minus 2 -
      (NCZornElement.mul (upperTwo a b)
        (NCZornElement.mul (upperTwo a b) (NCZornElement.pureNPlus d))).sigma_minus 2 =
      (a * b - b * a) * d
    rw [upperTwo_square_mul_pureNPlus_sigma_minus_two,
      upperTwo_mul_upperTwo_mul_pureNPlus_sigma_minus_two, sub_zero]
  refine ⟨hCoord, ?_⟩
  apply ncZornMulDefect_not_mem_range_of_associator_ne_zero (Z := NCZornElement.pureNPlus d)
  intro hZero
  have hZeroCoord := congrArg (fun W : OperatorZornMatrix A => W.sigma_minus 2) hZero
  exact h (hCoord.symm.trans hZeroCoord)

/-! ## 3. Characteristic-Free 3-Projection, Tripotent, 9-Block, and 5-Grade Structure -/

/-- The upper chiral sheet idempotent `(1, 0, 0, 0)`. -/
def ePlus : OperatorZornMatrix A :=
  nPlus (1 : A)

/-- The lower chiral sheet idempotent `(0, 1, 0, 0)`. -/
def eMinus : OperatorZornMatrix A :=
  nMinus (1 : A)

@[simp] theorem ePlus_n_plus : (ePlus : OperatorZornMatrix A).n_plus = 1 := rfl
@[simp] theorem ePlus_n_minus : (ePlus : OperatorZornMatrix A).n_minus = 0 := rfl
@[simp] theorem ePlus_sigma_plus : (ePlus : OperatorZornMatrix A).sigma_plus = 0 := rfl
@[simp] theorem ePlus_sigma_minus : (ePlus : OperatorZornMatrix A).sigma_minus = 0 := rfl
@[simp] theorem ePlus_sigma_plus_apply (i : Fin 3) :
    (ePlus : OperatorZornMatrix A).sigma_plus i = 0 := rfl
@[simp] theorem ePlus_sigma_minus_apply (i : Fin 3) :
    (ePlus : OperatorZornMatrix A).sigma_minus i = 0 := rfl

@[simp] theorem eMinus_n_plus : (eMinus : OperatorZornMatrix A).n_plus = 0 := rfl
@[simp] theorem eMinus_n_minus : (eMinus : OperatorZornMatrix A).n_minus = 1 := rfl
@[simp] theorem eMinus_sigma_plus : (eMinus : OperatorZornMatrix A).sigma_plus = 0 := rfl
@[simp] theorem eMinus_sigma_minus : (eMinus : OperatorZornMatrix A).sigma_minus = 0 := rfl
@[simp] theorem eMinus_sigma_plus_apply (i : Fin 3) :
    (eMinus : OperatorZornMatrix A).sigma_plus i = 0 := rfl
@[simp] theorem eMinus_sigma_minus_apply (i : Fin 3) :
    (eMinus : OperatorZornMatrix A).sigma_minus i = 0 := rfl

@[simp] theorem ePlus_add_eMinus :
    (ePlus : OperatorZornMatrix A) + eMinus = zornOne := by
  apply operatorZornMatrix_ext
  · simp [zornOne, diagonalCoefficient, operatorZornCoordinates]
  · simp [zornOne, diagonalCoefficient, operatorZornCoordinates]
  · funext i; simp [zornOne, diagonalCoefficient, operatorZornCoordinates]
  · funext i; simp [zornOne, diagonalCoefficient, operatorZornCoordinates]

/-- Projection onto the negative-charge sector `(0, 0, 0, σ₋)` (index `0`, degree `-1`). -/
def projMinus : Module.End ℤ (OperatorZornMatrix A) :=
  (AddMonoidHom.mk'
    (fun X : OperatorZornMatrix A => operatorZornCoordinates 0 0 0 X.sigma_minus)
    (fun X Y => by
      apply operatorZornMatrix_ext
      · simp [operatorZornCoordinates]
      · simp [operatorZornCoordinates]
      · funext i; simp [operatorZornCoordinates]
      · funext i; rfl)).toIntLinearMap

/-- Projection onto the neutral diagonal sector `(n₊, n₋, 0, 0)` (index `1`, degree `0`). -/
def projZero : Module.End ℤ (OperatorZornMatrix A) :=
  (AddMonoidHom.mk'
    (fun X : OperatorZornMatrix A => operatorZornCoordinates X.n_plus X.n_minus 0 0)
    (fun X Y => by
      apply operatorZornMatrix_ext
      · rfl
      · rfl
      · funext i; simp [operatorZornCoordinates]
      · funext i; simp [operatorZornCoordinates])).toIntLinearMap

/-- Projection onto the positive-charge sector `(0, 0, σ₊, 0)` (index `2`, degree `+1`). -/
def projPlus : Module.End ℤ (OperatorZornMatrix A) :=
  (AddMonoidHom.mk'
    (fun X : OperatorZornMatrix A => operatorZornCoordinates 0 0 X.sigma_plus 0)
    (fun X Y => by
      apply operatorZornMatrix_ext
      · simp [operatorZornCoordinates]
      · simp [operatorZornCoordinates]
      · funext i; rfl
      · funext i; simp [operatorZornCoordinates])).toIntLinearMap

@[simp] theorem projMinus_n_plus (X : OperatorZornMatrix A) : (projMinus X).n_plus = 0 := rfl
@[simp] theorem projMinus_n_minus (X : OperatorZornMatrix A) : (projMinus X).n_minus = 0 := rfl
@[simp] theorem projMinus_sigma_plus (X : OperatorZornMatrix A) : (projMinus X).sigma_plus = 0 := rfl
@[simp] theorem projMinus_sigma_minus (X : OperatorZornMatrix A) :
    (projMinus X).sigma_minus = X.sigma_minus := rfl
@[simp] theorem projMinus_sigma_plus_apply (X : OperatorZornMatrix A) (i : Fin 3) :
    (projMinus X).sigma_plus i = 0 := rfl
@[simp] theorem projMinus_sigma_minus_apply (X : OperatorZornMatrix A) (i : Fin 3) :
    (projMinus X).sigma_minus i = X.sigma_minus i := rfl

@[simp] theorem projZero_n_plus (X : OperatorZornMatrix A) : (projZero X).n_plus = X.n_plus := rfl
@[simp] theorem projZero_n_minus (X : OperatorZornMatrix A) : (projZero X).n_minus = X.n_minus := rfl
@[simp] theorem projZero_sigma_plus (X : OperatorZornMatrix A) : (projZero X).sigma_plus = 0 := rfl
@[simp] theorem projZero_sigma_minus (X : OperatorZornMatrix A) : (projZero X).sigma_minus = 0 := rfl
@[simp] theorem projZero_sigma_plus_apply (X : OperatorZornMatrix A) (i : Fin 3) :
    (projZero X).sigma_plus i = 0 := rfl
@[simp] theorem projZero_sigma_minus_apply (X : OperatorZornMatrix A) (i : Fin 3) :
    (projZero X).sigma_minus i = 0 := rfl

@[simp] theorem projPlus_n_plus (X : OperatorZornMatrix A) : (projPlus X).n_plus = 0 := rfl
@[simp] theorem projPlus_n_minus (X : OperatorZornMatrix A) : (projPlus X).n_minus = 0 := rfl
@[simp] theorem projPlus_sigma_plus (X : OperatorZornMatrix A) :
    (projPlus X).sigma_plus = X.sigma_plus := rfl
@[simp] theorem projPlus_sigma_minus (X : OperatorZornMatrix A) : (projPlus X).sigma_minus = 0 := rfl
@[simp] theorem projPlus_sigma_plus_apply (X : OperatorZornMatrix A) (i : Fin 3) :
    (projPlus X).sigma_plus i = X.sigma_plus i := rfl
@[simp] theorem projPlus_sigma_minus_apply (X : OperatorZornMatrix A) (i : Fin 3) :
    (projPlus X).sigma_minus i = 0 := rfl

/-- Each chiral sector projection is realized algebraically by left and right multiplication
by the sheet idempotents `ePlus` and `eMinus`, with no division by `2`. -/
theorem projPlus_eq_leftMul_rightMul :
    projPlus (A := A) = ncZornLeftMul ePlus * ncZornRightMul eMinus := by
  refine LinearMap.ext fun X => ?_
  apply operatorZornMatrix_ext
  · simp [NCZornElement.zornDot]
  · simp [NCZornElement.zornDot]
  · funext i; fin_cases i <;> simp [NCZornElement.zornCross]
  · funext i; fin_cases i <;> simp [NCZornElement.zornCross]

theorem projMinus_eq_leftMul_rightMul :
    projMinus (A := A) = ncZornLeftMul eMinus * ncZornRightMul ePlus := by
  refine LinearMap.ext fun X => ?_
  apply operatorZornMatrix_ext
  · simp [NCZornElement.zornDot]
  · simp [NCZornElement.zornDot]
  · funext i; fin_cases i <;> simp [NCZornElement.zornCross]
  · funext i; fin_cases i <;> simp [NCZornElement.zornCross]

theorem projZero_eq_leftMul_rightMul :
    projZero (A := A) =
      ncZornLeftMul ePlus * ncZornRightMul ePlus +
        ncZornLeftMul eMinus * ncZornRightMul eMinus := by
  refine LinearMap.ext fun X => ?_
  apply operatorZornMatrix_ext
  · simp [NCZornElement.zornDot]
  · simp [NCZornElement.zornDot]
  · funext i; fin_cases i <;> simp [NCZornElement.zornCross]
  · funext i; fin_cases i <;> simp [NCZornElement.zornCross]

/-- Ordered family of three orthogonal projections `![projMinus, projZero, projPlus]`. -/
def ncZornProj : Fin 3 → Module.End ℤ (OperatorZornMatrix A) :=
  ![projMinus, projZero, projPlus]

theorem ncZornProj_sum :
    ∑ i : Fin 3, ncZornProj (A := A) i = 1 := by
  refine LinearMap.ext fun X => ?_
  apply operatorZornMatrix_ext
  · simp [Fin.sum_univ_three, ncZornProj]
  · simp [Fin.sum_univ_three, ncZornProj]
  · funext i; simp [Fin.sum_univ_three, ncZornProj]
  · funext i; simp [Fin.sum_univ_three, ncZornProj]

theorem ncZornProj_mul (i j : Fin 3) :
    ncZornProj (A := A) i * ncZornProj (A := A) j =
      if i = j then ncZornProj (A := A) i else 0 := by
  fin_cases i <;> fin_cases j <;>
  · refine LinearMap.ext fun X => ?_
    apply operatorZornMatrix_ext
    · simp [ncZornProj]
    · simp [ncZornProj]
    · funext c; simp [ncZornProj]
    · funext c; simp [ncZornProj]

/-- The characteristic-free tripotent `τ = L_{e₊} - R_{e₊} = Π₊₁ - Π₋₁` in
`Module.End ℤ (OperatorZornMatrix A)`. -/
def ncZornTripotent : Module.End ℤ (OperatorZornMatrix A) :=
  ncZornLeftMul ePlus - ncZornRightMul ePlus

theorem ncZornTripotent_eq_projPlus_sub_projMinus :
    ncZornTripotent (A := A) = projPlus - projMinus := by
  refine LinearMap.ext fun X => ?_
  change ePlus * X + -(X * ePlus) = projPlus X + -projMinus X
  apply operatorZornMatrix_ext
  · simp [NCZornElement.zornDot]
  · simp [NCZornElement.zornDot]
  · funext i; fin_cases i <;> simp [NCZornElement.zornCross]
  · funext i; fin_cases i <;> simp [NCZornElement.zornCross]

theorem ncZornTripotent_apply (X : OperatorZornMatrix A) :
    ncZornTripotent X = operatorZornCoordinates 0 0 X.sigma_plus (-X.sigma_minus) := by
  rw [ncZornTripotent_eq_projPlus_sub_projMinus]
  apply operatorZornMatrix_ext
  · change (projPlus X - projMinus X).n_plus = 0
    simp
  · change (projPlus X - projMinus X).n_minus = 0
    simp
  · funext i
    change (projPlus X - projMinus X).sigma_plus i = X.sigma_plus i
    simp
  · funext i
    change (projPlus X - projMinus X).sigma_minus i = -X.sigma_minus i
    simp

theorem ncZornTripotent_sq :
    ncZornTripotent (A := A) * ncZornTripotent (A := A) = projPlus + projMinus := by
  rw [ncZornTripotent_eq_projPlus_sub_projMinus]
  change (ncZornProj (A := A) 2 - ncZornProj (A := A) 0) *
      (ncZornProj (A := A) 2 - ncZornProj (A := A) 0) =
    ncZornProj (A := A) 2 + ncZornProj (A := A) 0
  simp only [sub_mul, mul_sub, ncZornProj_mul, ite_true,
     show (2 : Fin 3) = 0 ↔ False by decide,
     show (0 : Fin 3) = 2 ↔ False by decide, ite_false]
  abel

/-- The integral tripotent law `τ³ = τ` holds over any noncommutative ring `[Ring A]`
without dividing by `2`. -/
theorem ncZornTripotent_cube :
    ncZornTripotent (A := A) * ncZornTripotent (A := A) * ncZornTripotent (A := A) =
      ncZornTripotent (A := A) := by
  rw [ncZornTripotent_sq, ncZornTripotent_eq_projPlus_sub_projMinus]
  change (ncZornProj (A := A) 2 + ncZornProj (A := A) 0) *
      (ncZornProj (A := A) 2 - ncZornProj (A := A) 0) =
    ncZornProj (A := A) 2 - ncZornProj (A := A) 0
  simp only [add_mul, mul_sub, ncZornProj_mul, ite_true,
    show (2 : Fin 3) = 0 ↔ False by decide,
    show (0 : Fin 3) = 2 ↔ False by decide, ite_false]
  abel

theorem ncZornTripotent_mul_proj (i : Fin 3) :
    ncZornTripotent (A := A) * ncZornProj (A := A) i =
      peirceDegree i • ncZornProj (A := A) i := by
  rw [ncZornTripotent_eq_projPlus_sub_projMinus, sub_mul]
  change ncZornProj 2 * ncZornProj i - ncZornProj 0 * ncZornProj i =
    peirceDegree i • ncZornProj i
  fin_cases i <;>
    simp [ncZornProj_mul, peirceDegree]

theorem ncZornProj_mul_tripotent (i : Fin 3) :
    ncZornProj (A := A) i * ncZornTripotent (A := A) =
      peirceDegree i • ncZornProj (A := A) i := by
  rw [ncZornTripotent_eq_projPlus_sub_projMinus, mul_sub]
  change ncZornProj i * ncZornProj 2 - ncZornProj i * ncZornProj 0 =
    peirceDegree i • ncZornProj i
  fin_cases i <;>
    simp [ncZornProj_mul, peirceDegree]

/-- The `(i, j)` Peirce block of an operator `K : Module.End ℤ (OperatorZornMatrix A)`. -/
def ncZornBlock (i j : Fin 3) (K : Module.End ℤ (OperatorZornMatrix A)) :
    Module.End ℤ (OperatorZornMatrix A) :=
  ncZornProj i * K * ncZornProj j

@[simp] theorem ncZornBlock_add (i j : Fin 3)
    (K L : Module.End ℤ (OperatorZornMatrix A)) :
    ncZornBlock i j (K + L) = ncZornBlock i j K + ncZornBlock i j L := by
  unfold ncZornBlock
  simp only [mul_add, add_mul]

theorem ncZornBlock_sum (K : Module.End ℤ (OperatorZornMatrix A)) :
    ∑ i : Fin 3, ∑ j : Fin 3, ncZornBlock i j K = K := by
  simp only [ncZornBlock, ← Finset.mul_sum, ← Finset.sum_mul]
  rw [ncZornProj_sum, one_mul, mul_one]

theorem ncZornBlock_extract (a b i j : Fin 3) (K : Module.End ℤ (OperatorZornMatrix A)) :
    ncZornBlock a b (ncZornBlock i j K) =
      if a = i ∧ j = b then ncZornBlock i j K else 0 := by
  unfold ncZornBlock
  rw [show ncZornProj a * (ncZornProj i * K * ncZornProj j) * ncZornProj b =
      (ncZornProj a * ncZornProj i) * K * (ncZornProj j * ncZornProj b) by
        simp only [mul_assoc]]
  rw [ncZornProj_mul, ncZornProj_mul]
  split_ifs <;> simp_all

theorem ncZornBlock_comm_tripotent (i j : Fin 3)
    (K : Module.End ℤ (OperatorZornMatrix A)) :
    PeirceSpine.comm (ncZornTripotent (A := A)) (ncZornBlock i j K) =
      (peirceDegree i - peirceDegree j) • ncZornBlock i j K := by
  unfold PeirceSpine.comm ncZornBlock
  rw [← mul_assoc (ncZornTripotent (A := A)), ← mul_assoc (ncZornTripotent (A := A)),
    ncZornTripotent_mul_proj, mul_assoc (ncZornProj i * K), ncZornProj_mul_tripotent]
  simp only [smul_mul_assoc, mul_smul_comm, sub_smul]

/-- The 5 integer-charge components `d ∈ Fin 5` (carrying charges `-2, -1, 0, +1, +2`)
of an arbitrary additive endomorphism `K : Module.End ℤ (OperatorZornMatrix A)`. -/
def ncZornFiveComponent (K : Module.End ℤ (OperatorZornMatrix A)) :
    Fin 5 → Module.End ℤ (OperatorZornMatrix A) :=
  ![ncZornBlock 0 2 K,
    ncZornBlock 0 1 K + ncZornBlock 1 2 K,
    ncZornBlock 0 0 K + ncZornBlock 1 1 K + ncZornBlock 2 2 K,
    ncZornBlock 1 0 K + ncZornBlock 2 1 K,
    ncZornBlock 2 0 K]

theorem ncZornFiveComponent_sum (K : Module.End ℤ (OperatorZornMatrix A)) :
    ∑ d : Fin 5, ncZornFiveComponent K d = K := by
  have h := ncZornBlock_sum K
  simp only [Fin.sum_univ_three] at h
  simp [Fin.sum_univ_succ, ncZornFiveComponent]
  abel_nf at h ⊢
  exact h

theorem ncZornFiveComponent_extract (d e : Fin 5)
    (K : Module.End ℤ (OperatorZornMatrix A)) :
    ncZornFiveComponent (ncZornFiveComponent K e) d =
      if d = e then ncZornFiveComponent K d else 0 := by
  fin_cases d <;> fin_cases e <;>
    simp [ncZornFiveComponent, ncZornBlock_extract]

/-- Every grade component `ncZornFiveComponent K d` is an exact commutator eigen-operator
of `ncZornTripotent` with integer charge `(d : ℤ) - 2 ∈ {-2, -1, 0, +1, +2}`. -/
theorem ncZornFiveComponent_comm_tripotent
    (K : Module.End ℤ (OperatorZornMatrix A)) (d : Fin 5) :
    PeirceSpine.comm (ncZornTripotent (A := A)) (ncZornFiveComponent K d) =
      ((d.val : ℤ) - 2) • ncZornFiveComponent K d := by
  have h00 := ncZornBlock_comm_tripotent 0 0 K
  have h01 := ncZornBlock_comm_tripotent 0 1 K
  have h02 := ncZornBlock_comm_tripotent 0 2 K
  have h10 := ncZornBlock_comm_tripotent 1 0 K
  have h11 := ncZornBlock_comm_tripotent 1 1 K
  have h12 := ncZornBlock_comm_tripotent 1 2 K
  have h20 := ncZornBlock_comm_tripotent 2 0 K
  have h21 := ncZornBlock_comm_tripotent 2 1 K
  have h22 := ncZornBlock_comm_tripotent 2 2 K
  norm_num [peirceDegree] at h00 h01 h02 h10 h11 h12 h20 h21 h22
  fin_cases d
  · simpa [ncZornFiveComponent] using h02
  · change PeirceSpine.comm (ncZornTripotent (A := A))
        (ncZornBlock 0 1 K + ncZornBlock 1 2 K) =
      ((1 : ℤ) - 2) • (ncZornBlock 0 1 K + ncZornBlock 1 2 K)
    have hAdd : PeirceSpine.comm (ncZornTripotent (A := A))
        (ncZornBlock 0 1 K + ncZornBlock 1 2 K) =
      PeirceSpine.comm (ncZornTripotent (A := A)) (ncZornBlock 0 1 K) +
        PeirceSpine.comm (ncZornTripotent (A := A)) (ncZornBlock 1 2 K) := by
      simp only [PeirceSpine.comm, mul_add, add_mul]; abel
    rw [hAdd, h01, h12]
    norm_num [neg_one_smul]
  · change PeirceSpine.comm (ncZornTripotent (A := A))
        (ncZornBlock 0 0 K + ncZornBlock 1 1 K + ncZornBlock 2 2 K) =
      ((2 : ℤ) - 2) • (ncZornBlock 0 0 K + ncZornBlock 1 1 K + ncZornBlock 2 2 K)
    have hAdd : PeirceSpine.comm (ncZornTripotent (A := A))
        (ncZornBlock 0 0 K + ncZornBlock 1 1 K + ncZornBlock 2 2 K) =
      PeirceSpine.comm (ncZornTripotent (A := A)) (ncZornBlock 0 0 K) +
        PeirceSpine.comm (ncZornTripotent (A := A)) (ncZornBlock 1 1 K) +
        PeirceSpine.comm (ncZornTripotent (A := A)) (ncZornBlock 2 2 K) := by
      simp only [PeirceSpine.comm, mul_add, add_mul]; abel
    rw [hAdd, h00, h11, h22]
    simp
  · change PeirceSpine.comm (ncZornTripotent (A := A))
        (ncZornBlock 1 0 K + ncZornBlock 2 1 K) =
      ((3 : ℤ) - 2) • (ncZornBlock 1 0 K + ncZornBlock 2 1 K)
    have hAdd : PeirceSpine.comm (ncZornTripotent (A := A))
        (ncZornBlock 1 0 K + ncZornBlock 2 1 K) =
      PeirceSpine.comm (ncZornTripotent (A := A)) (ncZornBlock 1 0 K) +
        PeirceSpine.comm (ncZornTripotent (A := A)) (ncZornBlock 2 1 K) := by
      simp only [PeirceSpine.comm, mul_add, add_mul]; abel
    rw [hAdd, h10, h21]
    simp
  · simpa [ncZornFiveComponent] using h20

/-- Universal quintic commutator annihilator `(ad τ)⁵ - 5 (ad τ)³ + 4 (ad τ) = 0` on
all of `Module.End ℤ (OperatorZornMatrix A)`. -/
theorem ncZornTripotent_comm_fifth (K : Module.End ℤ (OperatorZornMatrix A)) :
    PeirceSpine.comm (ncZornTripotent (A := A))
      (PeirceSpine.comm (ncZornTripotent (A := A))
        (PeirceSpine.comm (ncZornTripotent (A := A))
          (PeirceSpine.comm (ncZornTripotent (A := A))
            (PeirceSpine.comm (ncZornTripotent (A := A)) K)))) -
      (5 : ℤ) •
        PeirceSpine.comm (ncZornTripotent (A := A))
          (PeirceSpine.comm (ncZornTripotent (A := A))
            (PeirceSpine.comm (ncZornTripotent (A := A)) K)) +
      (4 : ℤ) • PeirceSpine.comm (ncZornTripotent (A := A)) K = 0 :=
  tripotent_comm_fifth (ncZornTripotent_cube (A := A)) K

/-! ## 4. Explicit 5-Grade Decomposition of Left Multiplication `ncZornLeftMul X` -/

/-- The five charge components `(-2, -1, 0, +1, +2)` of `ncZornLeftMul X` separate the
Zorn cross-product terms (`d = 0, 4`, i.e. charges `-2, +2`) from the `2 × 2` Peirce
matrix corners (`d = 1, 3`, i.e. charges `-1, +1`) and diagonal sheet multiplication
(`d = 2`, charge `0`). -/
theorem ncZornLeftMul_fiveComponent_explicit (X Y : OperatorZornMatrix A) :
    ncZornFiveComponent (ncZornLeftMul X) 0 Y =
      operatorZornCoordinates 0 0 0 (NCZornElement.zornCross X.sigma_plus Y.sigma_plus) ∧
    ncZornFiveComponent (ncZornLeftMul X) 1 Y =
      operatorZornCoordinates 0 (NCZornElement.zornDot X.sigma_minus Y.sigma_plus)
        0 (fun i => X.sigma_minus i * Y.n_plus) ∧
    ncZornFiveComponent (ncZornLeftMul X) 2 Y =
      operatorZornCoordinates (X.n_plus * Y.n_plus) (X.n_minus * Y.n_minus)
        (fun i => X.n_plus * Y.sigma_plus i) (fun i => X.n_minus * Y.sigma_minus i) ∧
    ncZornFiveComponent (ncZornLeftMul X) 3 Y =
      operatorZornCoordinates (NCZornElement.zornDot X.sigma_plus Y.sigma_minus) 0
        (fun i => X.sigma_plus i * Y.n_minus) 0 ∧
    ncZornFiveComponent (ncZornLeftMul X) 4 Y =
      operatorZornCoordinates 0 0
        (fun i => -NCZornElement.zornCross X.sigma_minus Y.sigma_minus i) 0 := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  all_goals
    apply operatorZornMatrix_ext
    · simp [ncZornFiveComponent, ncZornBlock, ncZornProj, operatorZornCoordinates,
        NCZornElement.zornDot]
    · simp [ncZornFiveComponent, ncZornBlock, ncZornProj, operatorZornCoordinates,
        NCZornElement.zornDot]
    · funext i
      fin_cases i <;>
        simp [ncZornFiveComponent, ncZornBlock, ncZornProj, operatorZornCoordinates,
          NCZornElement.zornCross]
    · funext i
      fin_cases i <;>
        simp [ncZornFiveComponent, ncZornBlock, ncZornProj, operatorZornCoordinates,
          NCZornElement.zornCross]

/-- Master synthesis theorem for Step 1: over any noncommutative ring `[Ring A]`, the
operator-valued Zorn carrier `OperatorZornMatrix A` carries a characteristic-free
tripotent `ncZornTripotent = L_{e₊} - R_{e₊}` whose 5-grade decomposition reconstructs
every `ℤ`-linear operator, satisfies the quintic commutator annihilator, separates the
cross-product grades `±2` from the Peirce matrix grades `-1, 0, +1`, and detects
nonassociative multiplication defects outside `range ncZornLeftMulHom`. -/
theorem ncZorn_operator_five_grade_and_defect_synthesis
    (X Y : OperatorZornMatrix A) (K : Module.End ℤ (OperatorZornMatrix A)) :
    ncZornTripotent (A := A) * ncZornTripotent (A := A) * ncZornTripotent (A := A) =
      ncZornTripotent (A := A) ∧
    (∑ d : Fin 5, ncZornFiveComponent K d = K) ∧
    (∀ d : Fin 5,
      PeirceSpine.comm (ncZornTripotent (A := A)) (ncZornFiveComponent K d) =
        ((d.val : ℤ) - 2) • ncZornFiveComponent K d) ∧
    (PeirceSpine.comm (ncZornTripotent (A := A))
      (PeirceSpine.comm (ncZornTripotent (A := A))
        (PeirceSpine.comm (ncZornTripotent (A := A))
          (PeirceSpine.comm (ncZornTripotent (A := A))
            (PeirceSpine.comm (ncZornTripotent (A := A)) K)))) -
      (5 : ℤ) •
        PeirceSpine.comm (ncZornTripotent (A := A))
          (PeirceSpine.comm (ncZornTripotent (A := A))
            (PeirceSpine.comm (ncZornTripotent (A := A)) K)) +
      (4 : ℤ) • PeirceSpine.comm (ncZornTripotent (A := A)) K = 0) ∧
    (ncZornMulDefect X Y ∈ LinearMap.range (ncZornLeftMulHom (A := A)) ↔
      ncZornMulDefect X Y = 0) :=
  ⟨ncZornTripotent_cube,
   ncZornFiveComponent_sum K,
   ncZornFiveComponent_comm_tripotent K,
   ncZornTripotent_comm_fifth K,
   ncZornMulDefect_mem_range_iff_eq_zero X Y⟩

end InfoGeometry.OperatorAlgebra.NCZornTripotentFiveGrading
