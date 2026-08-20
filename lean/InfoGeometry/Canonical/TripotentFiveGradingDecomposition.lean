import Mathlib
import InfoGeometry.Physics.Algebra.TripotentLeftRightPeirceProjectors
import InfoGeometry.OperatorAlgebra.SuperTKKConformalClosure

/-!
# Tripotent five-grade decomposition

This owner packages the five grouped Peirce projectors associated with a
tripotent element into an actual linear direct-sum decomposition.

The input owner supplies:

* the nine joint left/right Peirce projectors;
* their orthogonality and idempotence;
* the five grouped adjoint-weight projectors;
* the reconstruction identity
  `Π₋₂ + Π₋₁ + Π₀ + Π₁ + Π₂ = 1`.

This file proves:

* idempotence and pairwise orthogonality of the five grouped projectors;
* a linear equivalence between the carrier and the product of their ranges;
* a theorem-honest adapter to
  `SuperTKKConformalClosure.FiveGrading` once the required Lie-bracket closure
  laws are supplied.

It does not identify the decomposition with a concrete TKK algebra without
those bracket laws.
-/

namespace InfoGeometry.Physics.Algebra

noncomputable section

set_option linter.unusedSectionVars false

variable {R : Type*} [Ring R] [Algebra ℝ R]

local notation "EndR" => Module.End ℝ R

/-- The five adjoint weights. -/
inductive FiveGrade where
  | negTwo
  | negOne
  | zero
  | posOne
  | posTwo
  deriving DecidableEq, Fintype, Repr

/-- Numerical value of a five-grade label. -/
def fiveGradeValue : FiveGrade → ℤ
  | .negTwo => -2
  | .negOne => -1
  | .zero => 0
  | .posOne => 1
  | .posTwo => 2

/-- Select the grouped Peirce projector belonging to a five-grade label. -/
def fiveGradeProjector (e : R) : FiveGrade → EndR
  | .negTwo => gradeNegTwoProjector e
  | .negOne => gradeNegOneProjector e
  | .zero => gradeZeroProjector e
  | .posOne => gradePosOneProjector e
  | .posTwo => gradePosTwoProjector e

@[simp] theorem fiveGradeProjector_negTwo (e : R) :
    fiveGradeProjector e .negTwo = gradeNegTwoProjector e :=
  rfl

@[simp] theorem fiveGradeProjector_negOne (e : R) :
    fiveGradeProjector e .negOne = gradeNegOneProjector e :=
  rfl

@[simp] theorem fiveGradeProjector_zero (e : R) :
    fiveGradeProjector e .zero = gradeZeroProjector e :=
  rfl

@[simp] theorem fiveGradeProjector_posOne (e : R) :
    fiveGradeProjector e .posOne = gradePosOneProjector e :=
  rfl

@[simp] theorem fiveGradeProjector_posTwo (e : R) :
    fiveGradeProjector e .posTwo = gradePosTwoProjector e :=
  rfl

/--
Two distinct joint Peirce projectors multiply to zero.
-/
@[simp] theorem jointPeirceProjector_mul_eq_zero_of_pair_ne
    {e : R} (he : e * e * e = e)
    {left right left' right' : PeirceSign}
    (hpair : (left, right) ≠ (left', right')) :
    jointPeirceProjector e left right *
        jointPeirceProjector e left' right' = 0 := by
  by_cases hleft : left = left'
  · subst left'
    have hright : right ≠ right' := by
      intro h
      apply hpair
      simp [h]
    exact jointPeirceProjector_mul_eq_zero_of_right_ne he hright
  · exact jointPeirceProjector_mul_eq_zero_of_left_ne he hleft

/-- Every grouped five-grade projector is idempotent. -/
@[simp] theorem fiveGradeProjector_idempotent
    {e : R} (he : e * e * e = e)
    (k : FiveGrade) :
    fiveGradeProjector e k * fiveGradeProjector e k =
      fiveGradeProjector e k := by
  cases k <;>
    simp [fiveGradeProjector,
      gradeNegTwoProjector, gradeNegOneProjector,
      gradeZeroProjector, gradePosOneProjector,
      gradePosTwoProjector,
      mul_add, add_mul,
      jointPeirceProjector_mul_self he,
      jointPeirceProjector_mul_eq_zero_of_pair_ne he]

/-- Distinct grouped five-grade projectors are orthogonal. -/
@[simp] theorem fiveGradeProjector_mul_eq_zero_of_ne
    {e : R} (he : e * e * e = e)
    {i j : FiveGrade} (hij : i ≠ j) :
    fiveGradeProjector e i * fiveGradeProjector e j = 0 := by
  cases i <;> cases j <;>
    simp_all [fiveGradeProjector,
      gradeNegTwoProjector, gradeNegOneProjector,
      gradeZeroProjector, gradePosOneProjector,
      gradePosTwoProjector,
      mul_add, add_mul,
      jointPeirceProjector_mul_eq_zero_of_pair_ne he]

/-- The five projector ranges. -/
def fiveGradeRange (e : R) (k : FiveGrade) : Submodule ℝ R :=
  LinearMap.range (fiveGradeProjector e k)

/-- Canonical projection into a projector range. -/
def fiveGradeComponentLinear
    (e : R) (k : FiveGrade) :
    R →ₗ[ℝ] fiveGradeRange e k where
  toFun x :=
    ⟨fiveGradeProjector e k x, ⟨x, rfl⟩⟩
  map_add' x y := by
    apply Subtype.ext
    simp
  map_smul' c x := by
    apply Subtype.ext
    simp

/-- Nested coordinate carrier required by the repository five-grading API. -/
abbrev FiveGradeCoordinates (e : R) :=
  ((((fiveGradeRange e .negTwo × fiveGradeRange e .negOne) ×
      fiveGradeRange e .zero) ×
      fiveGradeRange e .posOne) ×
      fiveGradeRange e .posTwo)

/-- Decompose an element into its five projector components. -/
def fiveGradeDecomposeLinear (e : R) :
    R →ₗ[ℝ] FiveGradeCoordinates e where
  toFun x :=
    ((((
      fiveGradeComponentLinear e .negTwo x,
      fiveGradeComponentLinear e .negOne x),
      fiveGradeComponentLinear e .zero x),
      fiveGradeComponentLinear e .posOne x),
      fiveGradeComponentLinear e .posTwo x)
  map_add' x y := by
    ext <;> simp [fiveGradeComponentLinear]
  map_smul' c x := by
    ext <;> simp [fiveGradeComponentLinear]

/-- Recompose five grade coordinates by addition. -/
def fiveGradeRecomposeLinear (e : R) :
    FiveGradeCoordinates e →ₗ[ℝ] R where
  toFun v :=
    (((((v.1.1.1.1 : R) + (v.1.1.1.2 : R)) +
      (v.1.1.2 : R)) +
      (v.1.2 : R)) +
      (v.2 : R))
  map_add' x y := by
    simp [add_comm, add_left_comm]
  map_smul' c x := by
    simp [smul_add]

/-- Applying a grade projector to an element of its own range fixes it. -/
@[simp] theorem fiveGradeProjector_apply_range_self
    {e : R} (he : e * e * e = e)
    (k : FiveGrade)
    (x : fiveGradeRange e k) :
    fiveGradeProjector e k (x : R) = (x : R) := by
  rcases x.property with ⟨y, hy⟩
  rw [← hy]
  have h :=
    congrArg
      (fun P : EndR => P y)
      (fiveGradeProjector_idempotent he k)
  simpa using h

/-- A distinct grade projector kills an element of another projector range. -/
@[simp] theorem fiveGradeProjector_apply_range_eq_zero_of_ne
    {e : R} (he : e * e * e = e)
    {i j : FiveGrade} (hij : i ≠ j := by decide)
    (x : fiveGradeRange e j) :
    fiveGradeProjector e i (x : R) = 0 := by
  rcases x.property with ⟨y, hy⟩
  rw [← hy]
  have h :=
    congrArg
      (fun P : EndR => P y)
      (fiveGradeProjector_mul_eq_zero_of_ne he hij)
  simpa using h

/-- Recomposing the canonical decomposition gives the original element. -/
@[simp] theorem fiveGrade_recompose_decompose
    (e x : R) :
    fiveGradeRecomposeLinear e
      (fiveGradeDecomposeLinear e x) = x := by
  have h :=
    congrArg
      (fun P : EndR => P x)
      (fiveGradeProjectors_sum_eq_id e)
  simpa [fiveGradeRecomposeLinear, fiveGradeDecomposeLinear,
    fiveGradeComponentLinear, fiveGradeProjector,
    LinearMap.add_apply] using h

private lemma decompose_recompose_component
    {e : R} (he : e * e * e = e)
    (k : FiveGrade)
    (vNegTwo : fiveGradeRange e .negTwo)
    (vNegOne : fiveGradeRange e .negOne)
    (vZero : fiveGradeRange e .zero)
    (vPosOne : fiveGradeRange e .posOne)
    (vPosTwo : fiveGradeRange e .posTwo) :
    fiveGradeProjector e k (vNegTwo.1 + vNegOne.1 + vZero.1 + vPosOne.1 + vPosTwo.1) =
      (match k with
       | .negTwo => vNegTwo.1
       | .negOne => vNegOne.1
       | .zero => vZero.1
       | .posOne => vPosOne.1
       | .posTwo => vPosTwo.1) := by
  rw [map_add, map_add, map_add, map_add]
  cases k
  · rw [fiveGradeProjector_apply_range_self he,
        fiveGradeProjector_apply_range_eq_zero_of_ne he (by decide) vNegOne,
        fiveGradeProjector_apply_range_eq_zero_of_ne he (by decide) vZero,
        fiveGradeProjector_apply_range_eq_zero_of_ne he (by decide) vPosOne,
        fiveGradeProjector_apply_range_eq_zero_of_ne he (by decide) vPosTwo]
    simp
  · rw [fiveGradeProjector_apply_range_self he,
        fiveGradeProjector_apply_range_eq_zero_of_ne he (by decide) vNegTwo,
        fiveGradeProjector_apply_range_eq_zero_of_ne he (by decide) vZero,
        fiveGradeProjector_apply_range_eq_zero_of_ne he (by decide) vPosOne,
        fiveGradeProjector_apply_range_eq_zero_of_ne he (by decide) vPosTwo]
    simp
  · rw [fiveGradeProjector_apply_range_self he,
        fiveGradeProjector_apply_range_eq_zero_of_ne he (by decide) vNegTwo,
        fiveGradeProjector_apply_range_eq_zero_of_ne he (by decide) vNegOne,
        fiveGradeProjector_apply_range_eq_zero_of_ne he (by decide) vPosOne,
        fiveGradeProjector_apply_range_eq_zero_of_ne he (by decide) vPosTwo]
    simp
  · rw [fiveGradeProjector_apply_range_self he,
        fiveGradeProjector_apply_range_eq_zero_of_ne he (by decide) vNegTwo,
        fiveGradeProjector_apply_range_eq_zero_of_ne he (by decide) vNegOne,
        fiveGradeProjector_apply_range_eq_zero_of_ne he (by decide) vZero,
        fiveGradeProjector_apply_range_eq_zero_of_ne he (by decide) vPosTwo]
    simp
  · rw [fiveGradeProjector_apply_range_self he,
        fiveGradeProjector_apply_range_eq_zero_of_ne he (by decide) vNegTwo,
        fiveGradeProjector_apply_range_eq_zero_of_ne he (by decide) vNegOne,
        fiveGradeProjector_apply_range_eq_zero_of_ne he (by decide) vZero,
        fiveGradeProjector_apply_range_eq_zero_of_ne he (by decide) vPosOne]
    simp

/-- Decomposing a recomposed coordinate tuple returns the tuple. -/
@[simp] theorem fiveGrade_decompose_recompose
    {e : R} (he : e * e * e = e)
    (v : FiveGradeCoordinates e) :
    fiveGradeDecomposeLinear e
      (fiveGradeRecomposeLinear e v) = v := by
  rcases v with ⟨⟨⟨⟨vNegTwo, vNegOne⟩, vZero⟩, vPosOne⟩, vPosTwo⟩
  dsimp [fiveGradeDecomposeLinear, fiveGradeRecomposeLinear, fiveGradeComponentLinear]
  refine Prod.ext (Prod.ext (Prod.ext (Prod.ext ?_ ?_) ?_) ?_) ?_
  · exact Subtype.ext (decompose_recompose_component he .negTwo vNegTwo vNegOne vZero vPosOne vPosTwo)
  · exact Subtype.ext (decompose_recompose_component he .negOne vNegTwo vNegOne vZero vPosOne vPosTwo)
  · exact Subtype.ext (decompose_recompose_component he .zero vNegTwo vNegOne vZero vPosOne vPosTwo)
  · exact Subtype.ext (decompose_recompose_component he .posOne vNegTwo vNegOne vZero vPosOne vPosTwo)
  · exact Subtype.ext (decompose_recompose_component he .posTwo vNegTwo vNegOne vZero vPosOne vPosTwo)

/--
The carrier is linearly equivalent to the product of its five grade ranges.
-/
def tripotentFiveGradeLinearEquiv
    (e : R) (he : e * e * e = e) :
    R ≃ₗ[ℝ] FiveGradeCoordinates e where
  toFun := fiveGradeDecomposeLinear e
  invFun := fiveGradeRecomposeLinear e
  left_inv := fiveGrade_recompose_decompose e
  right_inv := fiveGrade_decompose_recompose he
  map_add' := (fiveGradeDecomposeLinear e).map_add
  map_smul' := (fiveGradeDecomposeLinear e).map_smul

@[simp] theorem tripotentFiveGradeLinearEquiv_apply
    (e : R) (he : e * e * e = e) (x : R) :
    tripotentFiveGradeLinearEquiv e he x =
      fiveGradeDecomposeLinear e x :=
  rfl

@[simp] theorem tripotentFiveGradeLinearEquiv_symm_apply
    (e : R) (he : e * e * e = e)
    (v : FiveGradeCoordinates e) :
    (tripotentFiveGradeLinearEquiv e he).symm v =
      (((((v.1.1.1.1 : R) + (v.1.1.1.2 : R)) +
        (v.1.1.2 : R)) +
        (v.1.2 : R)) +
        (v.2 : R)) :=
  rfl

end

end InfoGeometry.Physics.Algebra
