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

variable {R A : Type*} [CommSemiring R] [Ring A] [Algebra R A]

def leftAction (a : A) : A →ₗ[R] A := LinearMap.mulLeft R a

@[simp] theorem leftAction_apply (a x : A) : leftAction (R := R) a x = a * x := rfl

def rightAction (b : A) : A →ₗ[R] A := LinearMap.mulRight R b

@[simp] theorem rightAction_apply (b x : A) : rightAction (R := R) b x = x * b := rfl

def leftCommutant : Set (A →ₗ[R] A) :=
  {T | ∀ a : A, T.comp (leftAction a) = (leftAction a).comp T}

@[simp] theorem leftAction_one :
    leftAction (R := R) (1 : A) = LinearMap.id := by
  ext x
  simp [leftAction]

@[simp] theorem rightAction_one :
    rightAction (R := R) (1 : A) = LinearMap.id := by
  ext x
  simp [rightAction]

theorem leftAction_mul (a b : A) :
    leftAction (R := R) (a * b) =
      (leftAction (R := R) a).comp (leftAction (R := R) b) := by
  ext x
  simp [leftAction, LinearMap.comp_apply, mul_assoc]

theorem rightAction_mul (a b : A) :
    rightAction (R := R) (a * b) =
      (rightAction (R := R) b).comp (rightAction (R := R) a) := by
  ext x
  simp [rightAction, LinearMap.comp_apply, mul_assoc]

theorem leftAction_add (a b : A) :
    leftAction (R := R) (a + b) =
      leftAction (R := R) a + leftAction (R := R) b := by
  ext x
  simp [leftAction, add_mul]

theorem rightAction_add (a b : A) :
    rightAction (R := R) (a + b) =
      rightAction (R := R) a + rightAction (R := R) b := by
  ext x
  simp [rightAction, mul_add]

theorem leftAction_injective :
    Function.Injective (fun a : A => leftAction (R := R) a) := by
  intro a b h
  have h' := congrArg (fun T : A →ₗ[R] A => T 1) h
  simpa [leftAction] using h'

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

theorem leftAction_commutator (a b : A) :
    (leftAction (R := R) a).comp (leftAction (R := R) b) -
        (leftAction (R := R) b).comp (leftAction (R := R) a) =
      leftAction (R := R) (a * b - b * a) := by
  ext x
  simp [leftAction, LinearMap.comp_apply, sub_mul, mul_assoc]

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

end InfoGeometry.Physics.RegularBimoduleCommutant
