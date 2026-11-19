/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import Mathlib.Algebra.Algebra.Bilinear
import InfoGeometry.Algebra.FiniteSpinAlgebra

/-!
# Native regular-bimodule commutant equality

For a ring viewed as its own regular module, the commutant of all left
multiplications is exactly the right-regular action.  This is the concrete
commutant equality used by the opposite-frame/Morita bridge; it requires no
supplied Tomita or Hodge law.
-/

namespace InfoGeometry.Physics.RegularBimoduleCommutant

variable {R A : Type*} [Semiring R] [Ring A] [Module R A] [IsScalarTower R A A] [SMulCommClass R A A]

def leftAction (a : A) : A →ₗ[R] A := LinearMap.mulLeft R a

omit [IsScalarTower R A A] in
@[simp] theorem leftAction_apply (a x : A) : leftAction (R := R) a x = a * x := rfl

def rightAction (b : A) : A →ₗ[R] A := LinearMap.mulRight R b

omit [SMulCommClass R A A] in
@[simp] theorem rightAction_apply (b x : A) : rightAction (R := R) b x = x * b := rfl

def leftCommutant : Set (A →ₗ[R] A) :=
  {T | ∀ a : A, T.comp (leftAction a) = (leftAction a).comp T}

omit [IsScalarTower R A A] in
@[simp] theorem leftAction_one :
    leftAction (R := R) (1 : A) = LinearMap.id := by
  ext x
  simp [leftAction]

omit [SMulCommClass R A A] in
@[simp] theorem rightAction_one :
    rightAction (R := R) (1 : A) = LinearMap.id := by
  ext x
  simp [rightAction]

omit [IsScalarTower R A A] in
theorem leftAction_mul (a b : A) :
    leftAction (R := R) (a * b) =
      (leftAction (R := R) a).comp (leftAction (R := R) b) := by
  ext x
  simp [leftAction, LinearMap.comp_apply]

omit [SMulCommClass R A A] in
theorem rightAction_mul (a b : A) :
    rightAction (R := R) (a * b) =
      (rightAction (R := R) b).comp (rightAction (R := R) a) := by
  ext x
  simp [rightAction, LinearMap.comp_apply, mul_assoc]

omit [IsScalarTower R A A] in
theorem leftAction_add (a b : A) :
    leftAction (R := R) (a + b) =
      leftAction (R := R) a + leftAction (R := R) b := by
  ext x
  simp [leftAction, add_mul]

omit [SMulCommClass R A A] in
theorem rightAction_add (a b : A) :
    rightAction (R := R) (a + b) =
      rightAction (R := R) a + rightAction (R := R) b := by
  ext x
  simp [rightAction, mul_add]

omit [IsScalarTower R A A] in
theorem leftAction_injective :
    Function.Injective (fun a : A => leftAction (R := R) a) := by
  intro a b h
  have h' := congrArg (fun T : A →ₗ[R] A => T 1) h
  simpa [leftAction] using h'

omit [SMulCommClass R A A] in
theorem rightAction_injective :
    Function.Injective (fun b : A => rightAction (R := R) b) := by
  intro a b h
  have h' := congrArg (fun T : A →ₗ[R] A => T 1) h
  simpa [rightAction] using h'

theorem rightAction_mem_leftCommutant (b : A) :
    rightAction b ∈ leftCommutant (R := R) := by
  intro a
  ext x
  simp [leftAction, rightAction,
    LinearMap.comp_apply, mul_assoc]

theorem leftAction_comp_rightAction (a b : A) :
    (leftAction (R := R) a).comp (rightAction (R := R) b) =
      (rightAction (R := R) b).comp (leftAction (R := R) a) := by
  ext x
  simp [leftAction, rightAction, LinearMap.comp_apply, mul_assoc]

omit [IsScalarTower R A A] in
theorem leftAction_commutator (a b : A) :
    (leftAction (R := R) a).comp (leftAction (R := R) b) -
        (leftAction (R := R) b).comp (leftAction (R := R) a) =
      leftAction (R := R) (a * b - b * a) := by
  ext x
  simp [leftAction, LinearMap.comp_apply, sub_mul, mul_assoc]

omit [SMulCommClass R A A] in
theorem rightAction_commutator (a b : A) :
    (rightAction (R := R) a).comp (rightAction (R := R) b) -
        (rightAction (R := R) b).comp (rightAction (R := R) a) =
      -rightAction (R := R) (a * b - b * a) := by
  ext x
  simp [rightAction, LinearMap.comp_apply, mul_sub, mul_assoc]

theorem leftAction_eq_rightAction_of_commutes (a : A)
    (hcentral : ∀ x : A, a * x = x * a) :
    leftAction (R := R) a = rightAction (R := R) a := by
  ext x
  exact hcentral x

theorem leftCommutant_eq_rightActionRange :
    leftCommutant (R := R) = Set.range (fun b : A => rightAction (R := R) b) := by
  apply Set.Subset.antisymm
  · intro T hT
    refine ⟨T 1, ?_⟩
    ext x
    have hx := congrArg (fun f : A →ₗ[R] A => f 1) (hT x)
    simpa [leftAction, rightAction, LinearMap.comp_apply] using hx.symm
  · rintro T ⟨b, rfl⟩
    exact rightAction_mem_leftCommutant (R := R) b


/-- Right multiplication is unchanged by a complete left Kraus family.
The expression uses multiplication by `star (V i)`; it does not assume an
inner product or identify that multiplication with a Hilbert adjoint. -/
theorem rightAction_kraus_invariant [StarRing A] {ι : Type*} [Fintype ι]
    (V : ι → A) (B : A) (hV : ∑ i, star (V i) * V i = 1) :
    (∑ i, (leftAction (R := R) (star (V i))).comp
      ((rightAction (R := R) B).comp (leftAction (R := R) (V i)))) =
        rightAction (R := R) B := by
  ext x
  simp only [LinearMap.sum_apply, LinearMap.comp_apply,
    leftAction_apply, rightAction_apply]
  simp only [← mul_assoc, ← Finset.sum_mul, hV, one_mul]

/-- Star reflection changes left multiplication by `star a` into right
multiplication by `a`, with both conjugations written explicitly. -/
theorem star_leftAction_star [StarRing A] (a x : A) :
    star (leftAction (R := R) (star a) (star x)) = rightAction (R := R) a x := by
  simp only [leftAction_apply, rightAction_apply, star_mul, star_star]

end InfoGeometry.Physics.RegularBimoduleCommutant
