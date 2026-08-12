import Mathlib.Algebra.Algebra.Bilinear

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

def rightAction (b : A) : A →ₗ[R] A := LinearMap.mulRight R b

def leftCommutant : Set (A →ₗ[R] A) :=
  {T | ∀ a : A, T.comp (leftAction a) = (leftAction a).comp T}

theorem rightAction_mem_leftCommutant (b : A) :
    rightAction b ∈ leftCommutant (R := R) := by
  intro a
  ext x
  simp [leftAction, rightAction,
    LinearMap.comp_apply, mul_assoc]

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
