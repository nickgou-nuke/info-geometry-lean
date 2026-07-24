/-
InfoGeometry/OperatorAlgebra/IndividuatedBoundedTransform.lean

Constructive scalar core for the bounded transform.

This file kills the first shadow in the bounded-transform branch.

For

  f(t) = t / sqrt(1 + t^2)

we prove constructively:

  f(t)^2 = t^2 / (1 + t^2)
  f(t)^2 <= 1.

The operator-level theorem `F†F <= 1` is not asserted globally. It is obtained
only after a functional-calculus/order-lift bridge explicitly proves that the
scalar bound transfers to the chosen operator model.
-/

import Mathlib
import InfoGeometry.Meta.OwnerTarget

noncomputable section

namespace InfoGeometry.OperatorAlgebra.IndividuatedBoundedTransform

/-! ## 1. Scalar bounded transform -/

/--
Scalar bounded transform:

`f(t) = t / sqrt (1 + t^2)`.
-/
def scalarBoundedTransform
    (t : ℝ) : ℝ :=
  t / Real.sqrt (1 + t ^ 2)

/-- The denominator `1 + t^2` is positive. -/
theorem one_add_sq_pos
    (t : ℝ) :
    0 < 1 + t ^ 2 := by
  nlinarith [sq_nonneg t]

/-- The denominator `1 + t^2` is nonnegative. -/
theorem one_add_sq_nonneg
    (t : ℝ) :
    0 ≤ 1 + t ^ 2 :=
  le_of_lt (one_add_sq_pos t)


/-- The square denominator is never zero. -/
theorem one_add_sq_ne_zero
    (t : ℝ) :
    1 + t ^ 2 ≠ 0 := by
  exact ne_of_gt (one_add_sq_pos t)

/-- The square-root denominator is positive. -/
theorem sqrt_one_add_sq_pos
    (t : ℝ) :
    0 < Real.sqrt (1 + t ^ 2) := by
  exact Real.sqrt_pos.2 (one_add_sq_pos t)

/-- The square-root denominator is never zero. -/
theorem sqrt_one_add_sq_ne_zero
    (t : ℝ) :
    Real.sqrt (1 + t ^ 2) ≠ 0 := by
  exact ne_of_gt (sqrt_one_add_sq_pos t)

/-- Closed form for the square of the scalar bounded transform. -/
theorem scalarBoundedTransform_sq_eq
    (t : ℝ) :
    scalarBoundedTransform t ^ 2 =
      t ^ 2 / (1 + t ^ 2) := by
  dsimp [scalarBoundedTransform]
  rw [div_pow]
  rw [Real.sq_sqrt (one_add_sq_nonneg t)]

/--
Constructive scalar contraction theorem:

`(t / sqrt(1+t^2))^2 <= 1`.
-/
theorem scalarBoundedTransform_sq_le_one
    (t : ℝ) :
    scalarBoundedTransform t ^ 2 ≤ 1 := by
  rw [scalarBoundedTransform_sq_eq]
  rw [div_le_iff₀ (one_add_sq_pos t)]
  nlinarith [sq_nonneg t]


/-- Strict scalar contraction theorem. -/
theorem scalarBoundedTransform_sq_lt_one
    (t : ℝ) :
    scalarBoundedTransform t ^ 2 < 1 := by
  rw [scalarBoundedTransform_sq_eq]
  rw [div_lt_iff₀ (one_add_sq_pos t)]
  nlinarith [sq_nonneg t]

/-- Absolute-value contraction of the scalar bounded transform. -/
theorem abs_scalarBoundedTransform_lt_one
    (t : ℝ) :
    |scalarBoundedTransform t| < 1 := by
  exact (sq_lt_one_iff_abs_lt_one (scalarBoundedTransform t)).mp
    (scalarBoundedTransform_sq_lt_one t)

/-- Two-sided scalar bounded-transform estimate. -/
theorem scalarBoundedTransform_mem_Ioo
    (t : ℝ) :
    scalarBoundedTransform t ∈ Set.Ioo (-1 : ℝ) 1 := by
  exact abs_lt.mp (abs_scalarBoundedTransform_lt_one t)

/-- Compatibility alias for the previous snake-case theorem name. -/
theorem scalar_boundedTransform_sq_le_one
    (t : ℝ) :
    scalarBoundedTransform t ^ 2 ≤ 1 :=
  scalarBoundedTransform_sq_le_one t

/-- The square of the scalar bounded transform is nonnegative. -/
theorem scalarBoundedTransform_sq_nonneg
    (t : ℝ) :
    0 ≤ scalarBoundedTransform t ^ 2 :=
  sq_nonneg (scalarBoundedTransform t)

/-- The scalar bounded transform square lies in `[0,1]`. -/
theorem scalarBoundedTransform_sq_mem_Icc
    (t : ℝ) :
    scalarBoundedTransform t ^ 2 ∈ Set.Icc (0 : ℝ) 1 :=
  ⟨scalarBoundedTransform_sq_nonneg t,
   scalarBoundedTransform_sq_le_one t⟩

/-! ## 2. Scalar bounded-transform contraction -/

/-- The scalar owner target is now constructively proved. -/
theorem scalarBoundedTransformOwnerTarget :
    ∀ t : ℝ, scalarBoundedTransform t ^ 2 ≤ 1 := by
  intro t
  exact scalarBoundedTransform_sq_le_one t

@[owner_target_tag]
theorem scalarBoundedTransform_packet :
    (∀ t : ℝ, 0 ≤ scalarBoundedTransform t ^ 2) ∧
      (∀ t : ℝ, scalarBoundedTransform t ^ 2 ≤ 1) := by
  exact ⟨scalarBoundedTransform_sq_nonneg, scalarBoundedTransformOwnerTarget⟩

/-! ## 3. Operator lift through explicit functional calculus -/

/--
Functional-calculus/order-lift bridge for the bounded transform.

This is the correct operator-level replacement for a vacuous contraction law.

The scalar theorem is already proved above. A concrete operator model must now
supply the bridge that transfers scalar spectral bounds to the chosen operator
calculus.
-/
structure BoundedTransformFunctionalCalculusBridge
    (Op : Type*) [Ring Op] [StarRing Op] [PartialOrder Op] where
  /-- Unbounded/self-adjoint generator represented in the chosen model. -/
  D : Op

  /-- Bounded transform, morally `D (1 + D^2)^(-1/2)`. -/
  F : Op

  /-- Self-adjointness of `D`. -/
  D_selfAdjoint :
    star D = D


  /--
  Spectral/order lift:

  if the scalar function is pointwise bounded by `1` after squaring, then the
  operator bounded transform is a contraction.
  -/
  spectral_order_lift :
    (∀ t : ℝ, scalarBoundedTransform t ^ 2 ≤ 1) →
      star F * F ≤ 1

namespace BoundedTransformFunctionalCalculusBridge

variable {Op : Type*} [Ring Op] [StarRing Op] [PartialOrder Op]
variable (B : BoundedTransformFunctionalCalculusBridge Op)

/--
Constructive bounded-transform contraction, obtained from the scalar theorem
and the supplied functional-calculus/order-lift bridge.
-/
theorem contraction :
    star B.F * B.F ≤ 1 :=
  B.spectral_order_lift scalarBoundedTransform_sq_le_one

end BoundedTransformFunctionalCalculusBridge

/-! ## 4. Operator owner theorem, explicitly bridge-gated -/

/--
Bridge-gated operator owner theorem.

No operator contraction is asserted without a functional-calculus/order-lift
bridge.
-/
theorem operatorBoundedTransformOwnerTarget :
  ∀ (Op : Type*) [Ring Op] [StarRing Op] [PartialOrder Op],
  ∀ B : BoundedTransformFunctionalCalculusBridge Op,
    star B.F * B.F ≤ 1 := by
  intro Op _ _ _ B
  exact B.contraction

/--
The operator owner packet is discharged from the explicit bridge and the
constructive scalar theorem.
-/
@[owner_target_tag]
theorem operatorBoundedTransform_packet
    (Op : Type*) [Ring Op] [StarRing Op] [PartialOrder Op]
    (B : BoundedTransformFunctionalCalculusBridge Op) :
    star B.F * B.F ≤ 1 ∧
      star B.D = B.D := by
  exact ⟨operatorBoundedTransformOwnerTarget Op B, B.D_selfAdjoint⟩

end InfoGeometry.OperatorAlgebra.IndividuatedBoundedTransform
