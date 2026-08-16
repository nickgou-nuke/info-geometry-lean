import Mathlib
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

variable {R : Type*} [Ring R] [Algebra ℝ R]

local notation "EndR" => Module.End ℝ R

/-- Left multiplication by an algebra element. -/
abbrev leftMulOp (a : R) : EndR := leftMulLinear a

/-- Right multiplication by an algebra element. -/
abbrev rightMulOp (a : R) : EndR := rightMulLinear a

@[simp] theorem leftMulOp_apply (a x : R) :
    leftMulOp a x = a * x :=
  rfl

@[simp] theorem rightMulOp_apply (a x : R) :
    rightMulOp a x = x * a :=
  rfl

/-- Left and right multiplication commute in an associative algebra. -/
theorem leftMulOp_comp_rightMulOp (a b : R) :
    (leftMulOp a).comp (rightMulOp b) =
      (rightMulOp b).comp (leftMulOp a) := by
  ext x
  simp [mul_assoc]

/-- Tripotency passes to left multiplication. -/
theorem leftMulOp_tripotent
    {e : R} (he : e * e * e = e) :
    leftMulOp e * leftMulOp e * leftMulOp e =
      leftMulOp e := by
  ext x
  change e * (e * (e * x)) = e * x
  calc
    e * (e * (e * x)) = (e * e * e) * x := by simp [mul_assoc]
    _ = e * x := by rw [he]

/-- Tripotency passes to right multiplication. -/
theorem rightMulOp_tripotent
    {e : R} (he : e * e * e = e) :
    rightMulOp e * rightMulOp e * rightMulOp e =
      rightMulOp e := by
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

/-- The three projectors reconstruct the unit. -/
@[simp] theorem peirceProjectors_sum_eq_one (e : R) :
    peirceProjector e .pos +
        peirceProjector e .zero +
        peirceProjector e .neg = 1 := by
  simpa [peirceProjector] using (proj_sum_eq_id (T := e))

/-- Each selected projector is idempotent. -/
@[simp] theorem peirceProjector_idempotent
    {e : R} (he : e * e * e = e)
    (s : PeirceSign) :
    peirceProjector e s * peirceProjector e s =
      peirceProjector e s := by
  cases s with
  | pos => simpa [peirceProjector] using (projPos_idempotent he)
  | zero => simpa [peirceProjector] using (projZero_idempotent he)
  | neg => simpa [peirceProjector] using (projNeg_idempotent he)

/-- Distinct selected projectors are orthogonal in either ordered product. -/
@[simp] theorem peirceProjector_mul_eq_zero_of_ne
    {e : R} (he : e * e * e = e)
    {s t : PeirceSign} (hst : s ≠ t) :
    peirceProjector e s * peirceProjector e t = 0 := by
  cases s <;> cases t <;>
    simp_all [peirceProjector,
      projPos_mul_projNeg_eq_zero he,
      projNeg_mul_projPos_eq_zero he,
      projPos_mul_projZero_eq_zero he,
      projZero_mul_projPos_eq_zero he,
      projNeg_mul_projZero_eq_zero he,
      projZero_mul_projNeg_eq_zero he]

/-- Left spectral law for the selected projector. -/
@[simp] theorem e_mul_peirceProjector
    {e : R} (he : e * e * e = e)
    (s : PeirceSign) :
    e * peirceProjector e s =
      peirceScalar s • peirceProjector e s := by
  cases s with
  | pos => simpa [peirceProjector, peirceScalar] using (mul_projPos he)
  | zero => simpa [peirceProjector, peirceScalar] using (mul_projZero he)
  | neg => simpa [peirceProjector, peirceScalar] using (mul_projNeg he)

/-- Right spectral law for the selected projector. -/
@[simp] theorem peirceProjector_mul_e
    {e : R} (he : e * e * e = e)
    (s : PeirceSign) :
    peirceProjector e s * e =
      peirceScalar s • peirceProjector e s := by
  cases s with
  | pos => simpa [peirceProjector, peirceScalar] using (projPos_mul he)
  | zero => simpa [peirceProjector, peirceScalar] using (projZero_mul he)
  | neg => simpa [peirceProjector, peirceScalar] using (projNeg_mul he)

/-- Left Peirce projector acting on the algebra carrier. -/
def leftPeirceProjector (e : R) (s : PeirceSign) : EndR :=
  leftMulOp (peirceProjector e s)

/-- Right Peirce projector acting on the algebra carrier. -/
def rightPeirceProjector (e : R) (s : PeirceSign) : EndR :=
  rightMulOp (peirceProjector e s)

/-- Joint left/right Peirce projector. -/
def jointPeirceProjector
    (e : R) (left right : PeirceSign) : EndR :=
  (leftPeirceProjector e left).comp
    (rightPeirceProjector e right)

@[simp] theorem leftPeirceProjector_apply
    (e x : R) (s : PeirceSign) :
    leftPeirceProjector e s x = peirceProjector e s * x :=
  rfl

@[simp] theorem rightPeirceProjector_apply
    (e x : R) (s : PeirceSign) :
    rightPeirceProjector e s x = x * peirceProjector e s :=
  rfl

@[simp] theorem jointPeirceProjector_apply
    (e x : R) (left right : PeirceSign) :
    jointPeirceProjector e left right x =
      peirceProjector e left *
        (x * peirceProjector e right) :=
  rfl

/-- Every joint projector is idempotent. -/
@[simp] theorem jointPeirceProjector_idempotent
    {e : R} (he : e * e * e = e)
    (left right : PeirceSign) :
    jointPeirceProjector e left right *
        jointPeirceProjector e left right =
      jointPeirceProjector e left right := by
  ext x
  change
    peirceProjector e left *
        ((peirceProjector e left *
            (x * peirceProjector e right)) *
          peirceProjector e right) =
      peirceProjector e left *
        (x * peirceProjector e right)
  calc
    peirceProjector e left *
        ((peirceProjector e left *
            (x * peirceProjector e right)) *
          peirceProjector e right) =
      (peirceProjector e left * peirceProjector e left) *
        (x *
          (peirceProjector e right * peirceProjector e right)) := by
            noncomm_ring
    _ = peirceProjector e left *
        (x * peirceProjector e right) := by
          rw [peirceProjector_idempotent he,
            peirceProjector_idempotent he]

/-- Distinct left labels force orthogonality of joint projectors. -/
theorem jointPeirceProjector_mul_eq_zero_of_left_ne
    {e : R} (he : e * e * e = e)
    {left left' right right' : PeirceSign}
    (hleft : left ≠ left') :
    jointPeirceProjector e left right *
        jointPeirceProjector e left' right' = 0 := by
  ext x
  change
    peirceProjector e left *
        ((peirceProjector e left' *
            (x * peirceProjector e right')) *
          peirceProjector e right) = 0
  calc
    peirceProjector e left *
        ((peirceProjector e left' *
            (x * peirceProjector e right')) *
          peirceProjector e right) =
      (peirceProjector e left * peirceProjector e left') *
        (x *
          (peirceProjector e right' * peirceProjector e right)) := by
            noncomm_ring
    _ = 0 := by
      rw [peirceProjector_mul_eq_zero_of_ne he hleft]
      simp

/-- Distinct right labels force orthogonality of joint projectors. -/
theorem jointPeirceProjector_mul_eq_zero_of_right_ne
    {e : R} (he : e * e * e = e)
    {left left' right right' : PeirceSign}
    (hright : right ≠ right') :
    jointPeirceProjector e left right *
        jointPeirceProjector e left' right' = 0 := by
  ext x
  have hrev : right' ≠ right := by
    exact fun h => hright h.symm
  change
    peirceProjector e left *
        ((peirceProjector e left' *
            (x * peirceProjector e right')) *
          peirceProjector e right) = 0
  calc
    peirceProjector e left *
        ((peirceProjector e left' *
            (x * peirceProjector e right')) *
          peirceProjector e right) =
      (peirceProjector e left * peirceProjector e left') *
        (x *
          (peirceProjector e right' * peirceProjector e right)) := by
            noncomm_ring
    _ = 0 := by
      rw [peirceProjector_mul_eq_zero_of_ne he hrev]
      simp

/--
The nine joint Peirce components reconstruct every algebra element.
-/
theorem jointPeirce_reconstruction (e x : R) :
    jointPeirceProjector e .pos .pos x +
    jointPeirceProjector e .pos .zero x +
    jointPeirceProjector e .pos .neg x +
    jointPeirceProjector e .zero .pos x +
    jointPeirceProjector e .zero .zero x +
    jointPeirceProjector e .zero .neg x +
    jointPeirceProjector e .neg .pos x +
    jointPeirceProjector e .neg .zero x +
    jointPeirceProjector e .neg .neg x = x := by
  simp only [jointPeirceProjector_apply, peirceProjector]
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
    _ = x := by
      simp [proj_sum_eq_id (T := e)]

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
            rw [Algebra.smul_mul_assoc
              (peirceScalar left)
              (peirceProjector e left)
              (x * peirceProjector e right)]
            rw [Algebra.mul_smul_comm
              (peirceScalar right) x
              (peirceProjector e right)]
            rw [Algebra.mul_smul_comm
              (peirceScalar right)
              (peirceProjector e left)
              (x * peirceProjector e right)]
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
  simpa only [add_assoc, add_comm, add_left_comm] using h

/-- The grouped weight `+2` projector is idempotent. -/
@[simp] theorem gradePosTwoProjector_idempotent
    {e : R} (he : e * e * e = e) :
    gradePosTwoProjector e * gradePosTwoProjector e =
      gradePosTwoProjector e := by
  simpa [gradePosTwoProjector] using
    (jointPeirceProjector_idempotent he .pos .neg)

/-- The grouped weight `+1` projector is idempotent. -/
@[simp] theorem gradePosOneProjector_idempotent
    {e : R} (he : e * e * e = e) :
    gradePosOneProjector e * gradePosOneProjector e =
      gradePosOneProjector e := by
  dsimp [gradePosOneProjector]
  rw [add_mul, mul_add, mul_add]
  rw [jointPeirceProjector_idempotent he .pos .zero,
    jointPeirceProjector_idempotent he .zero .neg,
    jointPeirceProjector_mul_eq_zero_of_left_ne he (by decide : PeirceSign.pos ≠ .zero),
    jointPeirceProjector_mul_eq_zero_of_left_ne he (by decide : PeirceSign.zero ≠ .pos)]
  simp

/-- The grouped weight `0` projector is idempotent. -/
@[simp] theorem gradeZeroProjector_idempotent
    {e : R} (he : e * e * e = e) :
    gradeZeroProjector e * gradeZeroProjector e =
      gradeZeroProjector e := by
  dsimp [gradeZeroProjector]
  rw [add_mul, add_mul, mul_add, mul_add, mul_add, mul_add, mul_add, mul_add]
  rw [jointPeirceProjector_idempotent he .pos .pos,
    jointPeirceProjector_idempotent he .zero .zero,
    jointPeirceProjector_idempotent he .neg .neg,
    jointPeirceProjector_mul_eq_zero_of_left_ne he (by decide : PeirceSign.pos ≠ .zero),
    jointPeirceProjector_mul_eq_zero_of_left_ne he (by decide : PeirceSign.pos ≠ .neg),
    jointPeirceProjector_mul_eq_zero_of_left_ne he (by decide : PeirceSign.zero ≠ .pos),
    jointPeirceProjector_mul_eq_zero_of_left_ne he (by decide : PeirceSign.zero ≠ .neg),
    jointPeirceProjector_mul_eq_zero_of_left_ne he (by decide : PeirceSign.neg ≠ .pos),
    jointPeirceProjector_mul_eq_zero_of_left_ne he (by decide : PeirceSign.neg ≠ .zero)]
  simp

/-- The grouped weight `-1` projector is idempotent. -/
@[simp] theorem gradeNegOneProjector_idempotent
    {e : R} (he : e * e * e = e) :
    gradeNegOneProjector e * gradeNegOneProjector e =
      gradeNegOneProjector e := by
  dsimp [gradeNegOneProjector]
  rw [add_mul, mul_add, mul_add]
  rw [jointPeirceProjector_idempotent he .zero .pos,
    jointPeirceProjector_idempotent he .neg .zero,
    jointPeirceProjector_mul_eq_zero_of_left_ne he (by decide : PeirceSign.zero ≠ .neg),
    jointPeirceProjector_mul_eq_zero_of_left_ne he (by decide : PeirceSign.neg ≠ .zero)]
  simp

/-- The grouped weight `-2` projector is idempotent. -/
@[simp] theorem gradeNegTwoProjector_idempotent
    {e : R} (he : e * e * e = e) :
    gradeNegTwoProjector e * gradeNegTwoProjector e =
      gradeNegTwoProjector e := by
  simpa [gradeNegTwoProjector] using
    (jointPeirceProjector_idempotent he .neg .pos)

/-- All five adjoint-weight projectors are idempotent simultaneously. -/
theorem fiveGradeProjectors_idempotent
    {e : R} (he : e * e * e = e) :
    gradeNegTwoProjector e * gradeNegTwoProjector e = gradeNegTwoProjector e ∧
    gradeNegOneProjector e * gradeNegOneProjector e = gradeNegOneProjector e ∧
    gradeZeroProjector e * gradeZeroProjector e = gradeZeroProjector e ∧
    gradePosOneProjector e * gradePosOneProjector e = gradePosOneProjector e ∧
    gradePosTwoProjector e * gradePosTwoProjector e = gradePosTwoProjector e := by
  exact ⟨gradeNegTwoProjector_idempotent he,
    gradeNegOneProjector_idempotent he,
    gradeZeroProjector_idempotent he,
    gradePosOneProjector_idempotent he,
    gradePosTwoProjector_idempotent he⟩

@[simp] theorem gradePosTwo_adjoint_weight
    {e : R} (he : e * e * e = e) (x : R) :
    e * gradePosTwoProjector e x -
        gradePosTwoProjector e x * e =
      (2 : ℝ) • gradePosTwoProjector e x := by
  convert jointPeirceProjector_adjoint_weight he .pos .neg x using 1 <;>
    simp [gradePosTwoProjector, peirceScalar, add_smul] <;>
    rw [two_smul]

@[simp] theorem gradeNegTwo_adjoint_weight
    {e : R} (he : e * e * e = e) (x : R) :
    e * gradeNegTwoProjector e x -
        gradeNegTwoProjector e x * e =
      (-2 : ℝ) • gradeNegTwoProjector e x := by
  convert jointPeirceProjector_adjoint_weight he .neg .pos x using 1 <;>
    simp [gradeNegTwoProjector, peirceScalar, sub_eq_add_neg, add_smul,
      neg_smul] <;>
    rw [two_smul, neg_add]

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
    _ = (-1 : ℝ) • (a + b) := by simp

@[simp] theorem gradeZero_adjoint_weight
    {e : R} (he : e * e * e = e) (x : R) :
    e * gradeZeroProjector e x -
        gradeZeroProjector e x * e = 0 := by
  let a := jointPeirceProjector e .pos .pos x
  let b := jointPeirceProjector e .zero .zero x
  let c := jointPeirceProjector e .neg .neg x
  have ha := jointPeirceProjector_adjoint_weight he .pos .pos x
  have hb := jointPeirceProjector_adjoint_weight he .zero .zero x
  have hc := jointPeirceProjector_adjoint_weight he .neg .neg x
  change e * (a + b + c) - (a + b + c) * e = 0
  calc
    e * (a + b + c) - (a + b + c) * e =
        (e * a - a * e) +
          (e * b - b * e) +
          (e * c - c * e) := by
            noncomm_ring
    _ = 0 := by
      simpa [a, b, c, peirceScalar] using
        congrArg₂ (fun u v : R => u + v)
          (congrArg₂ (fun u v : R => u + v) ha hb) hc

end

end InfoGeometry.Physics.Algebra
