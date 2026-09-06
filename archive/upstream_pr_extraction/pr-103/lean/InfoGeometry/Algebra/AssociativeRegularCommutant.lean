import Mathlib.Algebra.Algebra.Basic

/-!
# The regular commutant of an associative algebra

On the regular left module `A`, right multiplication is exactly the
commutant of the left regular representation.  This is the elementary
evaluation-at-`1` theorem, stated once at the generic algebraic level.
-/

namespace InfoGeometry.Algebra.AssociativeRegularCommutant

variable {R A : Type*}
variable [CommSemiring R] [Semiring A] [Algebra R A]

def leftRegular (a : A) : Module.End R A :=
  LinearMap.mulLeft R a

def rightRegular (b : A) : Module.End R A :=
  LinearMap.mulRight R b

@[simp] theorem leftRegular_apply (a x : A) :
    leftRegular (R := R) a x = a * x := rfl

@[simp] theorem rightRegular_apply (b x : A) :
    rightRegular (R := R) b x = x * b := rfl

def leftRegularCommutant : Set (Module.End R A) :=
  {T | ∀ a x, T (leftRegular (R := R) a x) =
    leftRegular (R := R) a (T x)}

theorem rightRegular_mem_leftRegularCommutant (b : A) :
    rightRegular (R := R) b ∈ leftRegularCommutant (R := R) := by
  intro a x
  simp [mul_assoc]

theorem leftRegularCommutant_eq_rightRegular_range :
    leftRegularCommutant (R := R) (A := A) =
      {T | ∃ b : A, T = rightRegular (R := R) b} := by
  ext T
  constructor
  · intro hT
    refine ⟨T 1, ?_⟩
    apply LinearMap.ext
    intro x
    have hx := hT x 1
    simpa only [leftRegular_apply, rightRegular_apply, one_mul, mul_one] using hx
  · rintro ⟨b, rfl⟩
    exact rightRegular_mem_leftRegularCommutant (R := R) b

theorem rightRegular_injective :
    Function.Injective (rightRegular (R := R) : A → Module.End R A) := by
  intro a b hab
  have h := congrArg (fun T : Module.End R A => T 1) hab
  simpa only [rightRegular_apply, mul_one, one_mul] using h

end InfoGeometry.Algebra.AssociativeRegularCommutant
