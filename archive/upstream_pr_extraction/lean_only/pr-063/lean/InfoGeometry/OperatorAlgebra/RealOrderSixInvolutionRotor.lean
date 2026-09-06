import Mathlib.Algebra.Module.LinearMap.End
import Mathlib.Data.Real.Basic
import Mathlib.Tactic.NormNum

/-!
# Real order-six action from two involutions

The finite-order action here is an operator product of real linear
involutions.  No complex root of unity is used.  A Coxeter-type cube relation
for the product is recorded as data; the sixth-power law is then an ordinary
associative consequence.
-/

namespace InfoGeometry.OperatorAlgebra.RealOrderSixInvolutionRotor

variable {V : Type*} [AddCommGroup V] [Module ℝ V]

def rotor (first second : V ≃ₗ[ℝ] V) : Module.End ℝ V :=
  first.toLinearMap.comp second.toLinearMap

def reverseRotor (first second : V ≃ₗ[ℝ] V) : Module.End ℝ V :=
  second.toLinearMap.comp first.toLinearMap

@[simp] theorem rotor_apply (first second : V ≃ₗ[ℝ] V) (x : V) :
    rotor first second x = first (second x) :=
  rfl

@[simp] theorem reverseRotor_apply (first second : V ≃ₗ[ℝ] V) (x : V) :
    reverseRotor first second x = second (first x) :=
  rfl

theorem first_involutive (first : V ≃ₗ[ℝ] V)
    (hfirst : first.toLinearMap.comp first.toLinearMap = LinearMap.id) (x : V) :
    first (first x) = x := by
  have h := congrArg (fun f : Module.End ℝ V => f x) hfirst
  simpa [LinearMap.comp_apply] using h

theorem second_involutive (second : V ≃ₗ[ℝ] V)
    (hsecond : second.toLinearMap.comp second.toLinearMap = LinearMap.id) (x : V) :
    second (second x) = x := by
  have h := congrArg (fun f : Module.End ℝ V => f x) hsecond
  simpa [LinearMap.comp_apply] using h

theorem rotor_comp_reverseRotor (first second : V ≃ₗ[ℝ] V)
    (hfirst : first.toLinearMap.comp first.toLinearMap = LinearMap.id)
    (hsecond : second.toLinearMap.comp second.toLinearMap = LinearMap.id) :
    rotor first second * reverseRotor first second = LinearMap.id := by
  ext x
  change first (second (second (first x))) = x
  rw [second_involutive second hsecond, first_involutive first hfirst]

theorem reverseRotor_comp_rotor (first second : V ≃ₗ[ℝ] V)
    (hfirst : first.toLinearMap.comp first.toLinearMap = LinearMap.id)
    (hsecond : second.toLinearMap.comp second.toLinearMap = LinearMap.id) :
    reverseRotor first second * rotor first second = LinearMap.id := by
  ext x
  change second (first (first (second x))) = x
  rw [first_involutive first hfirst, second_involutive second hsecond]

theorem rotor_pow_six (first second : V ≃ₗ[ℝ] V)
    (hrotor : rotor first second ^ 3 = LinearMap.id) :
    rotor first second ^ 6 = LinearMap.id := by
  calc
    rotor first second ^ 6 = (rotor first second ^ 3) ^ 2 := by
      rw [show (6 : ℕ) = 3 * 2 by norm_num, pow_mul]
    _ = LinearMap.id := by rw [hrotor]; simp

theorem rotor_is_unit (first second : V ≃ₗ[ℝ] V)
    (hfirst : first.toLinearMap.comp first.toLinearMap = LinearMap.id)
    (hsecond : second.toLinearMap.comp second.toLinearMap = LinearMap.id) :
    Function.Bijective (rotor first second) := by
  refine ⟨?_, ?_⟩
  · intro x y hxy
    have h := congrArg (fun z => reverseRotor first second z) hxy
    simpa [Function.comp_def, ← LinearMap.comp_apply,
      reverseRotor_comp_rotor first second hfirst hsecond] using h
  · intro y
    refine ⟨reverseRotor first second y, ?_⟩
    change rotor first second (reverseRotor first second y) = y
    have h := congrArg (fun f : Module.End ℝ V => f y)
      (rotor_comp_reverseRotor first second hfirst hsecond)
    simpa using h

end InfoGeometry.OperatorAlgebra.RealOrderSixInvolutionRotor
