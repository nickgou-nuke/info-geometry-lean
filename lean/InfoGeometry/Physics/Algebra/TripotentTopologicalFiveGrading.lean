import Mathlib.Analysis.NormedSpace.OperatorNorm.Basic
import InfoGeometry.Physics.Algebra.TripotentFiveGradingDecomposition

/-!
# Continuous Peirce projectors

This file is the honest topological layer over the algebraic Peirce owner.
Multiplication is continuous in a normed algebra, so the left/right and joint
Peirce maps are continuous linear maps.  No completeness, exponential flow,
or automorphism theorem is asserted here.
-/

namespace InfoGeometry.Physics.Algebra

noncomputable section

variable {A : Type*} [NormedRing A] [NormedAlgebra ℝ A]

/-- Continuous left multiplication. -/
def continuousLeftMul (a : A) : A →L[ℝ] A :=
  (ContinuousLinearMap.mul ℝ A) a

/-- Continuous right multiplication, obtained from the native linear owner. -/
def continuousRightMul (b : A) : A →L[ℝ] A :=
  ContinuousLinearMap.mk (rightMulLinear b) (by
    simpa using
      ((continuous_id : Continuous (fun x : A => x)).mul
        (continuous_const : Continuous (fun _ : A => b))))

@[simp] theorem continuousLeftMul_apply (a x : A) :
    continuousLeftMul a x = a * x :=
  rfl

@[simp] theorem continuousRightMul_apply (b x : A) :
    continuousRightMul b x = x * b :=
  rfl

theorem continuousLeftMul_continuous (a : A) :
    Continuous (continuousLeftMul a) :=
  (continuousLeftMul a).continuous

theorem continuousRightMul_continuous (b : A) :
    Continuous (continuousRightMul b) :=
  (continuousRightMul b).continuous

/-- Continuous realization of the left Peirce projector. -/
def continuousLeftPeirceProjector (e : A) (s : PeirceSign) : A →L[ℝ] A :=
  continuousLeftMul (peirceProjector e s)

/-- Continuous realization of the right Peirce projector. -/
def continuousRightPeirceProjector (e : A) (s : PeirceSign) : A →L[ℝ] A :=
  continuousRightMul (peirceProjector e s)

/-- Continuous joint left/right Peirce projector. -/
def continuousJointPeirceProjector
    (e : A) (left right : PeirceSign) : A →L[ℝ] A :=
  (continuousLeftPeirceProjector e left).comp
    (continuousRightPeirceProjector e right)

@[simp] theorem continuousJointPeirceProjector_apply
    (e x : A) (left right : PeirceSign) :
    continuousJointPeirceProjector e left right x =
      jointPeirceProjector e left right x := by
  simp [continuousJointPeirceProjector, continuousLeftPeirceProjector,
    continuousRightPeirceProjector]

@[simp] theorem continuousJointPeirceProjector_idempotent
    {e : A} (he : e * e * e = e) (left right : PeirceSign) :
    continuousJointPeirceProjector e left right *
        continuousJointPeirceProjector e left right =
      continuousJointPeirceProjector e left right := by
  ext x
  have h := congrArg (fun f : Module.End ℝ A => f x)
    (jointPeirceProjector_idempotent (e := e) (left := left) (right := right) he)
  simpa [ContinuousLinearMap.mul_apply, continuousJointPeirceProjector_apply] using h

@[simp] theorem continuousJointPeirceProjector_mul_eq_zero_of_left_ne
    {e : A} (he : e * e * e = e) {left left' right right' : PeirceSign}
    (hleft : left ≠ left') :
    continuousJointPeirceProjector e left right *
        continuousJointPeirceProjector e left' right' =
      0 := by
  ext x
  have h := congrArg (fun f : Module.End ℝ A => f x)
    (jointPeirceProjector_mul_eq_zero_of_left_ne (e := e) he hleft
      (right := right) (right' := right'))
  simpa [ContinuousLinearMap.mul_apply, continuousJointPeirceProjector_apply] using h

@[simp] theorem continuousJointPeirceProjector_mul_eq_zero_of_right_ne
    {e : A} (he : e * e * e = e) {left left' right right' : PeirceSign}
    (hright : right ≠ right') :
    continuousJointPeirceProjector e left right *
        continuousJointPeirceProjector e left' right' =
      0 := by
  ext x
  have h := congrArg (fun f : Module.End ℝ A => f x)
    (jointPeirceProjector_mul_eq_zero_of_right_ne (e := e) he hright
      (left := left) (left' := left'))
  simpa [ContinuousLinearMap.mul_apply, continuousJointPeirceProjector_apply] using h

/-- Continuous grouped projector indexed by the five algebraic grades. -/
def continuousGradeProjector (e : A) (k : FiveGrade) : A →L[ℝ] A :=
  match k with
  | .negTwo => continuousJointPeirceProjector e .neg .pos
  | .negOne => continuousJointPeirceProjector e .zero .pos +
      continuousJointPeirceProjector e .neg .zero
  | .zero => continuousJointPeirceProjector e .pos .pos +
      continuousJointPeirceProjector e .zero .zero +
      continuousJointPeirceProjector e .neg .neg
  | .posOne => continuousJointPeirceProjector e .pos .zero +
      continuousJointPeirceProjector e .zero .neg
  | .posTwo => continuousJointPeirceProjector e .pos .neg

@[simp] theorem continuousGradeProjector_apply
    (e x : A) (k : FiveGrade) :
    continuousGradeProjector e k x =
      fiveGradeProjector e k x := by
  cases k <;>
    simp [continuousGradeProjector, fiveGradeProjector,
      gradeNegTwoProjector, gradeNegOneProjector, gradeZeroProjector,
      gradePosOneProjector, gradePosTwoProjector]

theorem continuousGradeProjector_continuous
    (e : A) (k : FiveGrade) :
    Continuous (continuousGradeProjector e k) :=
  (continuousGradeProjector e k).continuous

@[simp] theorem continuousGradeProjector_idempotent
    {e : A} (he : e * e * e = e) (k : FiveGrade) :
    continuousGradeProjector e k * continuousGradeProjector e k =
      continuousGradeProjector e k := by
  ext x
  have h := congrArg (fun f : Module.End ℝ A => f)
    (fiveGradeProjector_idempotent (e := e) he k)
  simpa [continuousGradeProjector_apply, ContinuousLinearMap.mul_apply] using
    congrArg (fun f : Module.End ℝ A => f x) h

@[simp] theorem continuousGradeProjector_mul_eq_zero_of_ne
    {e : A} (he : e * e * e = e) {i j : FiveGrade} (hij : i ≠ j) :
    continuousGradeProjector e i * continuousGradeProjector e j = 0 := by
  ext x
  have h := congrArg (fun f : Module.End ℝ A => f)
    (fiveGradeProjector_mul_eq_zero_of_ne (e := e) he hij)
  simpa [continuousGradeProjector_apply, ContinuousLinearMap.mul_apply] using
    congrArg (fun f : Module.End ℝ A => f x) h

theorem continuousGradeProjector_sum_eq_id (e : A) :
    continuousGradeProjector e .negTwo +
        continuousGradeProjector e .negOne +
        continuousGradeProjector e .zero +
        continuousGradeProjector e .posOne +
        continuousGradeProjector e .posTwo =
      ContinuousLinearMap.id ℝ A := by
  ext x
  simp only [ContinuousLinearMap.add_apply, ContinuousLinearMap.id_apply,
    continuousGradeProjector_apply]
  exact congrArg (fun f : Module.End ℝ A => f x)
    (fiveGradeProjectors_sum_eq_id e)

def continuousFiveGradeComponentLinear
    (e : A) (k : FiveGrade) :
    A →L[ℝ] fiveGradeRange e k :=
  ContinuousLinearMap.mk (fiveGradeComponentLinear e k) (by
    apply Continuous.subtype_mk
    have hEq : (fun x : A => fiveGradeProjector e k x) =
        continuousGradeProjector e k := by
      funext x
      symm
      exact continuousGradeProjector_apply e x k
    simpa [hEq] using (continuousGradeProjector_continuous (A := A) e k)
  )

theorem continuousFiveGradeDecomposeLinear
    (e : A) : Continuous (fiveGradeDecomposeLinear e) := by
  have hNegTwo : Continuous (fun x : A =>
      continuousFiveGradeComponentLinear (A := A) e .negTwo x) :=
    (continuousFiveGradeComponentLinear (A := A) e .negTwo).continuous
  have hNegOne : Continuous (fun x : A =>
      continuousFiveGradeComponentLinear (A := A) e .negOne x) :=
    (continuousFiveGradeComponentLinear (A := A) e .negOne).continuous
  have hZero : Continuous (fun x : A =>
      continuousFiveGradeComponentLinear (A := A) e .zero x) :=
    (continuousFiveGradeComponentLinear (A := A) e .zero).continuous
  have hPosOne : Continuous (fun x : A =>
      continuousFiveGradeComponentLinear (A := A) e .posOne x) :=
    (continuousFiveGradeComponentLinear (A := A) e .posOne).continuous
  have hPosTwo : Continuous (fun x : A =>
      continuousFiveGradeComponentLinear (A := A) e .posTwo x) :=
    (continuousFiveGradeComponentLinear (A := A) e .posTwo).continuous
  simpa [fiveGradeDecomposeLinear, continuousFiveGradeComponentLinear] using
    (((hNegTwo.prodMk hNegOne).prodMk hZero).prodMk hPosOne).prodMk hPosTwo

theorem continuousFiveGradeRecomposeLinear
    (e : A) : Continuous (fiveGradeRecomposeLinear e) := by
  have hNegTwo : Continuous (fun v : FiveGradeCoordinates e =>
      ((v.1.1.1.1 : fiveGradeRange e .negTwo) : A)) :=
    continuous_subtype_val.comp
      (continuous_fst.comp (continuous_fst.comp (continuous_fst.comp continuous_fst)))
  have hNegOne : Continuous (fun v : FiveGradeCoordinates e =>
      ((v.1.1.1.2 : fiveGradeRange e .negOne) : A)) :=
    continuous_subtype_val.comp
      (continuous_snd.comp (continuous_fst.comp (continuous_fst.comp continuous_fst)))
  have hZero : Continuous (fun v : FiveGradeCoordinates e =>
      ((v.1.1.2 : fiveGradeRange e .zero) : A)) :=
    continuous_subtype_val.comp
      (continuous_snd.comp (continuous_fst.comp continuous_fst))
  have hPosOne : Continuous (fun v : FiveGradeCoordinates e =>
      ((v.1.2 : fiveGradeRange e .posOne) : A)) :=
    continuous_subtype_val.comp (continuous_snd.comp continuous_fst)
  have hPosTwo : Continuous (fun v : FiveGradeCoordinates e =>
      ((v.2 : fiveGradeRange e .posTwo) : A)) :=
    continuous_subtype_val.comp continuous_snd
  change Continuous (fun v : FiveGradeCoordinates e =>
    (((((v.1.1.1.1 : A) + (v.1.1.1.2 : A)) + (v.1.1.2 : A)) +
      (v.1.2 : A)) + (v.2 : A)))
  exact (((hNegTwo.add hNegOne).add hZero).add hPosOne).add hPosTwo

noncomputable def continuousTripotentFiveGradeLinearEquiv
    (e : A) (he : e * e * e = e) :
    A ≃L[ℝ] FiveGradeCoordinates e :=
  { toLinearEquiv := tripotentFiveGradeLinearEquiv e he
    continuous_toFun := continuousFiveGradeDecomposeLinear e
    continuous_invFun := continuousFiveGradeRecomposeLinear e }

@[simp] theorem continuousTripotentFiveGradeLinearEquiv_apply
    (e : A) (he : e * e * e = e) (x : A) :
    continuousTripotentFiveGradeLinearEquiv (A := A) e he x =
      fiveGradeDecomposeLinear e x :=
  rfl

end
end InfoGeometry.Physics.Algebra
