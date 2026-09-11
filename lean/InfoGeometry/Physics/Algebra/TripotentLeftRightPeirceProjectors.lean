import Mathlib
import InfoGeometry.Algebra.FiniteSpinAlgebra
import InfoGeometry.Physics.TripotentAdjointDerivation
import InfoGeometry.Physics.Algebra.TripotentPeirceProjectors

/-!
# Left/right Peirce projectors for a tripotent element

Let `e` be a tripotent element of an associative real algebra:

`e * e * e = e`.

The element-level projectors from `TripotentPeirceProjectors` are applied by
left and right multiplication.  Their nine joint projectors act as

`x ↦ P_λ(e) * x * P_μ(e)`.

The adjoint weight of the `(λ, μ)` sector is `λ - μ`, so the nine sectors group
into five weights `-2, -1, 0, 1, 2`.

This owner proves the finite polynomial/projector calculus and the five
adjoint-weight grouping.  It does not yet identify the resulting decomposition
with a Tits--Kantor--Koecher algebra or construct a superalgebra parity.
-/

namespace InfoGeometry.Physics.Algebra

noncomputable section

set_option linter.unusedSectionVars false

variable {R : Type*} [Ring R] [Algebra ℝ R]

local notation "EndR" => Module.End ℝ R

/-- Left and right multiplication commute in an associative algebra. -/
theorem leftMulLinear_comp_rightMulLinear (a b : R) :
    (leftMulLinear a).comp (rightMulLinear b) =
      (rightMulLinear b).comp (leftMulLinear a) := by
  ext x
  simp [mul_assoc]

/-- Tripotency passes to left multiplication. -/
theorem leftMulLinear_tripotent
    {e : R} (he : e * e * e = e) :
    leftMulLinear e * leftMulLinear e * leftMulLinear e =
      leftMulLinear e := by
  ext x
  change e * (e * (e * x)) = e * x
  calc
    e * (e * (e * x)) = (e * e * e) * x := by simp [mul_assoc]
    _ = e * x := by rw [he]

/-- Tripotency passes to right multiplication. -/
theorem rightMulLinear_tripotent
    {e : R} (he : e * e * e = e) :
    rightMulLinear e * rightMulLinear e * rightMulLinear e =
      rightMulLinear e := by
  ext x
  change ((x * e) * e) * e = x * e
  calc
    ((x * e) * e) * e = x * (e * e * e) := by simp [mul_assoc]
    _ = x * e := by rw [he]

/-- The three Peirce labels. -/
inductive PeirceSign where
  | pos
  | zero
  | neg
  deriving DecidableEq, Fintype, Repr

/-- Scalar eigenvalue attached to a Peirce label. -/
def peirceScalar : PeirceSign → ℝ
  | .pos => 1
  | .zero => 0
  | .neg => -1

/-- Element-level projector selected by a Peirce label. -/
def peirceProjector (e : R) : PeirceSign → R
  | .pos => projPos e
  | .zero => projZero e
  | .neg => projNeg e

@[simp] theorem peirceProjector_pos (e : R) :
    peirceProjector e .pos = projPos e :=
  rfl

@[simp] theorem peirceProjector_zero (e : R) :
    peirceProjector e .zero = projZero e :=
  rfl

@[simp] theorem peirceProjector_neg (e : R) :
    peirceProjector e .neg = projNeg e :=
  rfl

/-! ## Elementary eigenvalue properties -/

@[simp] theorem e_mul_peirceProjector
    {e : R} (he : e * e * e = e) (s : PeirceSign) :
    e * peirceProjector e s =
      peirceScalar s • peirceProjector e s := by
  cases s
  · simpa [peirceScalar] using mul_projPos he
  · simpa [peirceScalar] using mul_projZero he
  · simpa [peirceScalar] using mul_projNeg he

@[simp] theorem peirceProjector_mul_e
    {e : R} (he : e * e * e = e) (s : PeirceSign) :
    peirceProjector e s * e =
      peirceScalar s • peirceProjector e s := by
  cases s
  · simpa [peirceScalar] using projPos_mul he
  · simpa [peirceScalar] using projZero_mul he
  · simpa [peirceScalar] using projNeg_mul he

/-! ## Left/right Peirce operators -/

/-- Left Peirce projector. -/
def peirceLeft (e : R) (s : PeirceSign) : EndR :=
  leftMulLinear (peirceProjector e s)

/-- Right Peirce projector. -/
def peirceRight (e : R) (s : PeirceSign) : EndR :=
  rightMulLinear (peirceProjector e s)

/-- Joint Peirce projector `P_{λ, μ}(x) = P_λ * x * P_μ`. -/
def jointPeirceProjector
    (e : R) (left right : PeirceSign) : EndR :=
  (peirceLeft e left).comp (peirceRight e right)

@[simp] theorem jointPeirceProjector_apply
    (e : R) (left right : PeirceSign) (x : R) :
    jointPeirceProjector e left right x =
      peirceProjector e left * (x * peirceProjector e right) :=
  rfl

/-- Left and right Peirce projectors commute. -/
theorem peirceLeft_comp_peirceRight
    (e : R) (left right : PeirceSign) :
    (peirceLeft e left).comp (peirceRight e right) =
      (peirceRight e right).comp (peirceLeft e left) :=
  leftMulLinear_comp_rightMulLinear _ _

/-! ## Idempotence and orthogonality -/

@[simp] theorem peirceProjector_mul_self
    {e : R} (he : e * e * e = e) (s : PeirceSign) :
    peirceProjector e s * peirceProjector e s =
      peirceProjector e s := by
  cases s
  · exact projPos_idempotent he
  · exact projZero_idempotent he
  · exact projNeg_idempotent he

theorem peirceProjector_mul_eq_zero_of_ne
    {e : R} (he : e * e * e = e)
    {s₁ s₂ : PeirceSign} (hne : s₁ ≠ s₂) :
    peirceProjector e s₁ * peirceProjector e s₂ = 0 := by
  cases s₁ <;> cases s₂ <;> try contradiction
  · exact projPos_mul_projZero_eq_zero he
  · exact projPos_mul_projNeg_eq_zero he
  · exact projZero_mul_projPos_eq_zero he
  · exact projZero_mul_projNeg_eq_zero he
  · exact projNeg_mul_projPos_eq_zero he
  · exact projNeg_mul_projZero_eq_zero he

@[simp] theorem peirceLeft_mul_self
    {e : R} (he : e * e * e = e) (s : PeirceSign) :
    peirceLeft e s * peirceLeft e s = peirceLeft e s := by
  ext x
  simp only [peirceLeft, leftMulLinear_apply, Module.End.mul_apply]
  rw [← mul_assoc, peirceProjector_mul_self he]

@[simp] theorem peirceRight_mul_self
    {e : R} (he : e * e * e = e) (s : PeirceSign) :
    peirceRight e s * peirceRight e s = peirceRight e s := by
  ext x
  simp only [peirceRight, rightMulLinear_apply, Module.End.mul_apply]
  rw [mul_assoc, peirceProjector_mul_self he]

@[simp] theorem jointPeirceProjector_mul_self
    {e : R} (he : e * e * e = e) (left right : PeirceSign) :
    jointPeirceProjector e left right *
        jointPeirceProjector e left right =
      jointPeirceProjector e left right := by
  ext x
  calc
    jointPeirceProjector e left right (jointPeirceProjector e left right x) =
      peirceProjector e left *
        ((peirceProjector e left * (x * peirceProjector e right)) *
          peirceProjector e right) := rfl
    _ = (peirceProjector e left * peirceProjector e left) *
        x *
        (peirceProjector e right * peirceProjector e right) := by
          simp [mul_assoc]
    _ = peirceProjector e left * (x * peirceProjector e right) := by
      rw [peirceProjector_mul_self he, peirceProjector_mul_self he]
      simp [mul_assoc]

theorem jointPeirceProjector_mul_eq_zero_of_left_ne
    {e : R} (he : e * e * e = e)
    {left₁ left₂ right₁ right₂ : PeirceSign}
    (hne : left₁ ≠ left₂) :
    jointPeirceProjector e left₁ right₁ *
        jointPeirceProjector e left₂ right₂ = 0 := by
  ext x
  calc
    (jointPeirceProjector e left₁ right₁ *
        jointPeirceProjector e left₂ right₂) x =
      peirceProjector e left₁ *
        ((peirceProjector e left₂ * (x * peirceProjector e right₂)) *
          peirceProjector e right₁) := rfl
    _ = (peirceProjector e left₁ * peirceProjector e left₂) *
        (x * peirceProjector e right₂) *
        peirceProjector e right₁ := by
          simp [mul_assoc]
    _ = 0 := by
      rw [peirceProjector_mul_eq_zero_of_ne he hne, zero_mul, zero_mul]

theorem jointPeirceProjector_mul_eq_zero_of_right_ne
    {e : R} (he : e * e * e = e)
    {left₁ left₂ right₁ right₂ : PeirceSign}
    (hne : right₁ ≠ right₂) :
    jointPeirceProjector e left₁ right₁ *
        jointPeirceProjector e left₂ right₂ = 0 := by
  ext x
  calc
    (jointPeirceProjector e left₁ right₁ *
        jointPeirceProjector e left₂ right₂) x =
      peirceProjector e left₁ *
        ((peirceProjector e left₂ * (x * peirceProjector e right₂)) *
          peirceProjector e right₁) := rfl
    _ = peirceProjector e left₁ *
        (peirceProjector e left₂ * x *
          (peirceProjector e right₂ * peirceProjector e right₁)) := by
            simp [mul_assoc]
    _ = 0 := by
      rw [peirceProjector_mul_eq_zero_of_ne he (Ne.symm hne), mul_zero, mul_zero]

/-! ## Reconstruction identity -/

/-- The nine joint Peirce components reconstruct the element `x`. -/
theorem jointPeirce_reconstruction (e x : R) :
    jointPeirceProjector e .pos .pos x +
        jointPeirceProjector e .pos .zero x +
        jointPeirceProjector e .pos .neg x +
        jointPeirceProjector e .zero .pos x +
        jointPeirceProjector e .zero .zero x +
        jointPeirceProjector e .zero .neg x +
        jointPeirceProjector e .neg .pos x +
        jointPeirceProjector e .neg .zero x +
        jointPeirceProjector e .neg .neg x =
      x := by
  simp only [jointPeirceProjector_apply, peirceProjector_pos,
    peirceProjector_zero, peirceProjector_neg]
  have hsum : projPos e + projZero e + projNeg e = 1 := proj_sum_eq_id (T := e)
  calc
    projPos e * (x * projPos e) +
        projPos e * (x * projZero e) +
        projPos e * (x * projNeg e) +
        projZero e * (x * projPos e) +
        projZero e * (x * projZero e) +
        projZero e * (x * projNeg e) +
        projNeg e * (x * projPos e) +
        projNeg e * (x * projZero e) +
        projNeg e * (x * projNeg e) =
      (projPos e + projZero e + projNeg e) *
        x * (projPos e + projZero e + projNeg e) := by
          noncomm_ring
    _ = 1 * x * 1 := by rw [hsum]
    _ = x := by simp

/-- Adjoint weight of a joint Peirce component. -/
theorem jointPeirceProjector_adjoint_weight
    {e : R} (he : e * e * e = e)
    (left right : PeirceSign) (x : R) :
    e * jointPeirceProjector e left right x -
        jointPeirceProjector e left right x * e =
      (peirceScalar left - peirceScalar right) •
        jointPeirceProjector e left right x := by
  rw [jointPeirceProjector_apply]
  calc
    e * (peirceProjector e left *
          (x * peirceProjector e right)) -
        (peirceProjector e left *
          (x * peirceProjector e right)) * e =
      (e * peirceProjector e left) *
          (x * peirceProjector e right) -
        peirceProjector e left *
          (x * (peirceProjector e right * e)) := by
            simp [mul_assoc]
    _ = (peirceScalar left • peirceProjector e left) *
          (x * peirceProjector e right) -
        peirceProjector e left *
          (x * (peirceScalar right • peirceProjector e right)) := by
            rw [e_mul_peirceProjector he,
              peirceProjector_mul_e he]
    _ = peirceScalar left •
          (peirceProjector e left *
            (x * peirceProjector e right)) -
        peirceScalar right •
          (peirceProjector e left *
            (x * peirceProjector e right)) := by
            rw [smul_mul_assoc, mul_smul_comm, mul_smul_comm]
    _ = (peirceScalar left - peirceScalar right) •
          (peirceProjector e left *
            (x * peirceProjector e right)) := by
            rw [sub_smul]
    _ = (peirceScalar left - peirceScalar right) •
          jointPeirceProjector e left right x := by
            rfl

/-! ## Five grouped adjoint-weight projectors -/

/-- Weight `+2`: `(+, -)`. -/
def gradePosTwoProjector (e : R) : EndR :=
  jointPeirceProjector e .pos .neg

/-- Weight `+1`: `(+, 0) ⊕ (0, -)`. -/
def gradePosOneProjector (e : R) : EndR :=
  jointPeirceProjector e .pos .zero +
    jointPeirceProjector e .zero .neg

/-- Weight `0`: `(+, +) ⊕ (0, 0) ⊕ (-, -)`. -/
def gradeZeroProjector (e : R) : EndR :=
  jointPeirceProjector e .pos .pos +
    jointPeirceProjector e .zero .zero +
    jointPeirceProjector e .neg .neg

/-- Weight `-1`: `(0, +) ⊕ (-, 0)`. -/
def gradeNegOneProjector (e : R) : EndR :=
  jointPeirceProjector e .zero .pos +
    jointPeirceProjector e .neg .zero

/-- Weight `-2`: `(-, +)`. -/
def gradeNegTwoProjector (e : R) : EndR :=
  jointPeirceProjector e .neg .pos

/-- The five grouped projectors reconstruct the identity operator. -/
theorem fiveGradeProjectors_sum_eq_id (e : R) :
    gradeNegTwoProjector e +
        gradeNegOneProjector e +
        gradeZeroProjector e +
        gradePosOneProjector e +
        gradePosTwoProjector e =
      LinearMap.id := by
  ext x
  simp only [gradeNegTwoProjector, gradeNegOneProjector,
    gradeZeroProjector, gradePosOneProjector, gradePosTwoProjector,
    LinearMap.add_apply, LinearMap.id_apply]
  have h := jointPeirce_reconstruction e x
  calc
    jointPeirceProjector e .neg .pos x +
        (jointPeirceProjector e .zero .pos x + jointPeirceProjector e .neg .zero x) +
        (jointPeirceProjector e .pos .pos x + jointPeirceProjector e .zero .zero x + jointPeirceProjector e .neg .neg x) +
        (jointPeirceProjector e .pos .zero x + jointPeirceProjector e .zero .neg x) +
        jointPeirceProjector e .pos .neg x =
      jointPeirceProjector e .pos .pos x +
        jointPeirceProjector e .pos .zero x +
        jointPeirceProjector e .pos .neg x +
        jointPeirceProjector e .zero .pos x +
        jointPeirceProjector e .zero .zero x +
        jointPeirceProjector e .zero .neg x +
        jointPeirceProjector e .neg .pos x +
        jointPeirceProjector e .neg .zero x +
        jointPeirceProjector e .neg .neg x := by abel
    _ = x := h

@[simp] theorem gradePosTwo_adjoint_weight
    {e : R} (he : e * e * e = e) (x : R) :
    e * gradePosTwoProjector e x -
        gradePosTwoProjector e x * e =
      (2 : ℝ) • gradePosTwoProjector e x := by
  have h := jointPeirceProjector_adjoint_weight he .pos .neg x
  dsimp [gradePosTwoProjector, peirceScalar] at h ⊢
  norm_num at h
  exact h

@[simp] theorem gradeNegTwo_adjoint_weight
    {e : R} (he : e * e * e = e) (x : R) :
    e * gradeNegTwoProjector e x -
        gradeNegTwoProjector e x * e =
      (-2 : ℝ) • gradeNegTwoProjector e x := by
  have h := jointPeirceProjector_adjoint_weight he .neg .pos x
  dsimp [gradeNegTwoProjector, peirceScalar] at h ⊢
  rw [show ((-1 : ℝ) - 1) = -2 by norm_num] at h
  exact h

@[simp] theorem gradePosOne_adjoint_weight
    {e : R} (he : e * e * e = e) (x : R) :
    e * gradePosOneProjector e x -
        gradePosOneProjector e x * e =
      (1 : ℝ) • gradePosOneProjector e x := by
  let a := jointPeirceProjector e .pos .zero x
  let b := jointPeirceProjector e .zero .neg x
  have ha := jointPeirceProjector_adjoint_weight he .pos .zero x
  have hb := jointPeirceProjector_adjoint_weight he .zero .neg x
  change e * (a + b) - (a + b) * e = (1 : ℝ) • (a + b)
  calc
    e * (a + b) - (a + b) * e =
        (e * a - a * e) + (e * b - b * e) := by
          noncomm_ring
    _ = a + b := by
      simpa [a, b, peirceScalar] using
        congrArg₂ (fun u v : R => u + v) ha hb
    _ = (1 : ℝ) • (a + b) := by simp

@[simp] theorem gradeNegOne_adjoint_weight
    {e : R} (he : e * e * e = e) (x : R) :
    e * gradeNegOneProjector e x -
        gradeNegOneProjector e x * e =
      (-1 : ℝ) • gradeNegOneProjector e x := by
  let a := jointPeirceProjector e .zero .pos x
  let b := jointPeirceProjector e .neg .zero x
  have ha := jointPeirceProjector_adjoint_weight he .zero .pos x
  have hb := jointPeirceProjector_adjoint_weight he .neg .zero x
  change e * (a + b) - (a + b) * e = (-1 : ℝ) • (a + b)
  calc
    e * (a + b) - (a + b) * e =
        (e * a - a * e) + (e * b - b * e) := by
          noncomm_ring
    _ = -a + -b := by
      simpa [a, b, peirceScalar] using
        congrArg₂ (fun u v : R => u + v) ha hb
    _ = (-1 : ℝ) • (a + b) := by
      simp

@[simp] theorem gradeZero_adjoint_weight
    {e : R} (he : e * e * e = e) (x : R) :
    e * gradeZeroProjector e x -
        gradeZeroProjector e x * e =
      (0 : ℝ) • gradeZeroProjector e x := by
  let a := jointPeirceProjector e .pos .pos x
  let b := jointPeirceProjector e .zero .zero x
  let c := jointPeirceProjector e .neg .neg x
  have ha := jointPeirceProjector_adjoint_weight he .pos .pos x
  have hb := jointPeirceProjector_adjoint_weight he .zero .zero x
  have hc := jointPeirceProjector_adjoint_weight he .neg .neg x
  change e * (a + b + c) - (a + b + c) * e = (0 : ℝ) • (a + b + c)
  calc
    e * (a + b + c) - (a + b + c) * e =
        (e * a - a * e) + (e * b - b * e) + (e * c - c * e) := by
          noncomm_ring
    _ = 0 := by
      simpa [a, b, c, peirceScalar] using
        congrArg₂ (fun u v : R => u + v)
          (congrArg₂ (fun u v : R => u + v) ha hb) hc
    _ = (0 : ℝ) • (a + b + c) := by simp

end

end InfoGeometry.Physics.Algebra
