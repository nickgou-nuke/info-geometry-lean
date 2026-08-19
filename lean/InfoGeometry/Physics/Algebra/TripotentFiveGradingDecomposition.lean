import Mathlib
import InfoGeometry.Physics.Algebra.TripotentLeftRightPeirceProjectors
import InfoGeometry.OperatorAlgebra.SuperTKKConformalClosure

/-!
# Tripotent five-grade decomposition

The five grouped Peirce projectors give a genuine linear decomposition into
their ranges.  A TKK/Lie five-grading is packaged only after its bracket
closure laws are supplied explicitly.
-/

namespace InfoGeometry.Physics.Algebra

noncomputable section

variable {R : Type*} [Ring R] [Algebra ℝ R]

inductive FiveGrade where
  | negTwo | negOne | zero | posOne | posTwo
  deriving DecidableEq, Fintype, Repr

def fiveGradeValue : FiveGrade → ℤ
  | .negTwo => -2 | .negOne => -1 | .zero => 0 | .posOne => 1 | .posTwo => 2

def fiveGradeProjector (e : R) : FiveGrade → Module.End ℝ R
  | .negTwo => gradeNegTwoProjector e
  | .negOne => gradeNegOneProjector e
  | .zero => gradeZeroProjector e
  | .posOne => gradePosOneProjector e
  | .posTwo => gradePosTwoProjector e

@[simp] theorem fiveGradeProjector_idempotent
    {e : R} (he : e * e * e = e) (k : FiveGrade) :
    fiveGradeProjector e k * fiveGradeProjector e k =
      fiveGradeProjector e k := by
  cases k <;>
    simp [fiveGradeProjector, gradeNegTwoProjector,
      gradeNegOneProjector, gradeZeroProjector,
      gradePosOneProjector, gradePosTwoProjector,
      mul_add, add_mul, jointPeirceProjector_idempotent he,
      jointPeirceProjector_mul_eq_zero_of_left_ne he,
      jointPeirceProjector_mul_eq_zero_of_right_ne he]

@[simp] theorem fiveGradeProjector_mul_eq_zero_of_ne
    {e : R} (he : e * e * e = e) {i j : FiveGrade} (hij : i ≠ j) :
    fiveGradeProjector e i * fiveGradeProjector e j = 0 := by
  cases i <;> cases j <;>
    simp_all [fiveGradeProjector, gradeNegTwoProjector,
      gradeNegOneProjector, gradeZeroProjector,
      gradePosOneProjector, gradePosTwoProjector,
      mul_add, add_mul,
      jointPeirceProjector_mul_eq_zero_of_left_ne he,
      jointPeirceProjector_mul_eq_zero_of_right_ne he]

def fiveGradeRange (e : R) (k : FiveGrade) : Submodule ℝ R :=
  LinearMap.range (fiveGradeProjector e k)

def fiveGradeComponentLinear (e : R) (k : FiveGrade) :
    R →ₗ[ℝ] fiveGradeRange e k where
  toFun x := ⟨fiveGradeProjector e k x, ⟨x, rfl⟩⟩
  map_add' x y := by ext; simp
  map_smul' c x := by ext; simp

abbrev FiveGradeCoordinates (e : R) :=
  (((fiveGradeRange e .negTwo × fiveGradeRange e .negOne) ×
      fiveGradeRange e .zero) × fiveGradeRange e .posOne) ×
      fiveGradeRange e .posTwo

def fiveGradeDecomposeLinear (e : R) : R →ₗ[ℝ] FiveGradeCoordinates e where
  toFun x := (((((fiveGradeComponentLinear e .negTwo x,
      fiveGradeComponentLinear e .negOne x),
      fiveGradeComponentLinear e .zero x),
      fiveGradeComponentLinear e .posOne x),
      fiveGradeComponentLinear e .posTwo x))
  map_add' x y := by ext <;> simp [fiveGradeComponentLinear]
  map_smul' c x := by ext <;> simp [fiveGradeComponentLinear]

def fiveGradeRecomposeLinear (e : R) : FiveGradeCoordinates e →ₗ[ℝ] R where
  toFun v := (((((v.1.1.1.1 : R) + (v.1.1.1.2 : R)) +
      (v.1.1.2 : R)) + (v.1.2 : R)) + (v.2 : R))
  map_add' x y := by simp [add_assoc, add_comm, add_left_comm]
  map_smul' c x := by simp [smul_add]

@[simp] theorem fiveGradeProjector_apply_range_self
    {e : R} (he : e * e * e = e) (k : FiveGrade)
    (x : fiveGradeRange e k) :
    fiveGradeProjector e k (x : R) = (x : R) := by
  rcases x.property with ⟨y, hy⟩
  rw [← hy]
  have h := congrArg (fun P : Module.End ℝ R => P y)
    (fiveGradeProjector_idempotent he k)
  simpa using h

@[simp] theorem fiveGradeProjector_apply_range_eq_zero_of_ne
    {e : R} (he : e * e * e = e) {i j : FiveGrade} (hij : i ≠ j)
    (x : fiveGradeRange e j) :
    fiveGradeProjector e i (x : R) = 0 := by
  rcases x.property with ⟨y, hy⟩
  rw [← hy]
  have h := congrArg (fun P : Module.End ℝ R => P y)
    (fiveGradeProjector_mul_eq_zero_of_ne he hij)
  simpa using h

@[simp] theorem fiveGrade_recompose_decompose (e x : R) :
    fiveGradeRecomposeLinear e (fiveGradeDecomposeLinear e x) = x := by
  have h := congrArg (fun P : Module.End ℝ R => P x)
    (fiveGradeProjectors_sum_eq_id e)
  simpa [fiveGradeRecomposeLinear, fiveGradeDecomposeLinear,
    fiveGradeComponentLinear, fiveGradeProjector,
    LinearMap.add_apply] using h

@[simp] theorem fiveGrade_decompose_recompose
    {e : R} (he : e * e * e = e) (v : FiveGradeCoordinates e) :
    fiveGradeDecomposeLinear e (fiveGradeRecomposeLinear e v) = v := by
  rcases v with ⟨⟨⟨⟨vNegTwo, vNegOne⟩, vZero⟩, vPosOne⟩, vPosTwo⟩
  ext <;>
    simp [fiveGradeDecomposeLinear, fiveGradeRecomposeLinear,
      fiveGradeComponentLinear,
      fiveGradeProjector_apply_range_self he,
      fiveGradeProjector_apply_range_eq_zero_of_ne he,
      add_assoc, add_comm, add_left_comm]

def tripotentFiveGradeLinearEquiv (e : R) (he : e * e * e = e) :
    R ≃ₗ[ℝ] FiveGradeCoordinates e where
  toFun := fiveGradeDecomposeLinear e
  invFun := fiveGradeRecomposeLinear e
  left_inv := fiveGrade_recompose_decompose e
  right_inv := fiveGrade_decompose_recompose he
  map_add' := (fiveGradeDecomposeLinear e).map_add
  map_smul' := (fiveGradeDecomposeLinear e).map_smul

@[simp] theorem tripotentFiveGradeLinearEquiv_apply
    (e : R) (he : e * e * e = e) (x : R) :
    tripotentFiveGradeLinearEquiv e he x = fiveGradeDecomposeLinear e x := rfl

def TripotentFiveGradeBracketLaws (e : R) : Prop :=
  (∀ X Y : R,
    X ∈ fiveGradeRange e .negOne → Y ∈ fiveGradeRange e .posOne →
      ⁅X, Y⁆ ∈ fiveGradeRange e .zero) ∧
  (∀ X Y : R,
    X ∈ fiveGradeRange e .zero → Y ∈ fiveGradeRange e .zero →
      ⁅X, Y⁆ ∈ fiveGradeRange e .zero) ∧
  (∀ X Y : R,
    X ∈ fiveGradeRange e .posOne → Y ∈ fiveGradeRange e .posOne →
      ⁅X, Y⁆ ∈ fiveGradeRange e .posTwo) ∧
  (∀ X Y : R,
    X ∈ fiveGradeRange e .negOne → Y ∈ fiveGradeRange e .negOne →
      ⁅X, Y⁆ ∈ fiveGradeRange e .negTwo) ∧
  (∀ X Y : R,
    X ∈ fiveGradeRange e .zero → Y ∈ fiveGradeRange e .posTwo →
      ⁅X, Y⁆ ∈ fiveGradeRange e .posTwo) ∧
  (∀ X Y : R,
    X ∈ fiveGradeRange e .zero → Y ∈ fiveGradeRange e .negTwo →
      ⁅X, Y⁆ ∈ fiveGradeRange e .negTwo) ∧
  (∀ X Y : R,
    X ∈ fiveGradeRange e .posTwo → Y ∈ fiveGradeRange e .posTwo → ⁅X, Y⁆ = 0)

def tripotentFiveGrading
    (e : R) (he : e * e * e = e)
    (H : TripotentFiveGradeBracketLaws e) :
    InfoGeometry.OperatorAlgebra.SuperTKKConformalClosure.FiveGrading R where
  gNegTwo := fiveGradeRange e .negTwo
  gNegOne := fiveGradeRange e .negOne
  gZero := fiveGradeRange e .zero
  gPosOne := fiveGradeRange e .posOne
  gPosTwo := fiveGradeRange e .posTwo
  decomposition := tripotentFiveGradeLinearEquiv e he
  decomposition_symm_apply := by intro v; rfl
  bracket_neg_one_pos_one := H.1
  bracket_zero_zero := H.2.1
  bracket_pos_one_pos_one := H.2.2.1
  bracket_neg_one_neg_one := H.2.2.2.1
  bracket_zero_pos_two := H.2.2.2.2.1
  bracket_zero_neg_two := H.2.2.2.2.2.1
  bracket_pos_two_pos_two_zero := H.2.2.2.2.2.2

end
end InfoGeometry.Physics.Algebra
