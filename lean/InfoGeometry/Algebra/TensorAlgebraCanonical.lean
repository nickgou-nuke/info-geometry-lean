import Mathlib.LinearAlgebra.TensorAlgebra.Basic
import Mathlib.LinearAlgebra.TensorAlgebra.Grading
import Mathlib.LinearAlgebra.TensorAlgebra.ToTensorPower
import Mathlib.LinearAlgebra.ExteriorAlgebra.Basic
import Mathlib.LinearAlgebra.ExteriorPower.Basic
import Mathlib.LinearAlgebra.CliffordAlgebra.Basic
import Mathlib.LinearAlgebra.SymmetricAlgebra.Basic

set_option autoImplicit false

open scoped DirectSum TensorProduct

namespace TensorAlgebraCanonical

section Basic

variable {R M A : Type*}
variable [CommSemiring R]
variable [AddCommMonoid M] [Module R M]
variable [Semiring A] [Algebra R A]

abbrev TA : Type _ := TensorAlgebra R M

def includeLinear : M →ₗ[R] TensorAlgebra R M :=
  TensorAlgebra.ι R

def liftLinear (f : M →ₗ[R] A) : TensorAlgebra R M →ₐ[R] A :=
  TensorAlgebra.lift R f

@[simp]
theorem liftLinear_includeLinear (f : M →ₗ[R] A) (x : M) :
    liftLinear f (includeLinear x) = f x := by
  exact TensorAlgebra.lift_ι_apply f x

@[simp]
theorem liftLinear_comp_includeLinear (f : M →ₗ[R] A) :
    (liftLinear f).toLinearMap.comp includeLinear = f := by
  exact TensorAlgebra.ι_comp_lift f

theorem liftLinear_unique (f : M →ₗ[R] A) (g : TensorAlgebra R M →ₐ[R] A) :
    g.toLinearMap.comp includeLinear = f ↔ g = liftLinear f := by
  exact TensorAlgebra.lift_unique f g

theorem algHom_ext_from_include
    {f g : TensorAlgebra R M →ₐ[R] A}
    (h : f.toLinearMap.comp includeLinear = g.toLinearMap.comp includeLinear) :
    f = g := by
  exact TensorAlgebra.hom_ext h

@[simp]
theorem liftLinear_comp_include_of_algHom (g : TensorAlgebra R M →ₐ[R] A) :
    liftLinear (g.toLinearMap.comp includeLinear) = g := by
  exact TensorAlgebra.lift_comp_ι g

@[simp]
theorem includeLinear_inj (x y : M) :
    includeLinear (R := R) x = includeLinear (R := R) y ↔ x = y := by
  exact TensorAlgebra.ι_inj R x y

@[simp]
theorem includeLinear_eq_zero (x : M) :
    includeLinear (R := R) x = 0 ↔ x = 0 := by
  exact TensorAlgebra.ι_eq_zero_iff R x

@[simp]
theorem algebraMap_tensorAlgebra_inj (r s : R) :
    algebraMap R (TensorAlgebra R M) r = algebraMap R (TensorAlgebra R M) s ↔ r = s := by
  exact TensorAlgebra.algebraMap_inj M r s

@[simp]
theorem algebraMap_tensorAlgebra_eq_zero (r : R) :
    algebraMap R (TensorAlgebra R M) r = 0 ↔ r = 0 := by
  exact TensorAlgebra.algebraMap_eq_zero_iff M r

end Basic

section Induction

variable {R M : Type*}
variable [CommSemiring R]
variable [AddCommMonoid M] [Module R M]

@[elab_as_elim]
theorem tensorAlgebra_induction {C : TensorAlgebra R M → Prop}
    (h_scalar : ∀ r : R, C (algebraMap R (TensorAlgebra R M) r))
    (h_include : ∀ x : M, C (TensorAlgebra.ι R x))
    (h_mul : ∀ a b : TensorAlgebra R M, C a → C b → C (a * b))
    (h_add : ∀ a b : TensorAlgebra R M, C a → C b → C (a + b))
    (a : TensorAlgebra R M) : C a := by
  exact TensorAlgebra.induction h_scalar h_include h_mul h_add a

end Induction

section TensorPowers

variable {R M : Type*}
variable [CommSemiring R]
variable [AddCommMonoid M] [Module R M]

abbrev TensorPower (n : ℕ) : Type _ := ⨂[R]^n M

abbrev TensorPowerSum : Type _ := ⨁ n : ℕ, ⨂[R]^n M

def toTensorPowerSum : TensorAlgebra R M →ₐ[R] TensorPowerSum (R := R) (M := M) :=
  TensorAlgebra.toDirectSum

def ofTensorPowerSum : TensorPowerSum (R := R) (M := M) →ₐ[R] TensorAlgebra R M :=
  TensorAlgebra.ofDirectSum

def tensorAlgebraEquivTensorPowerSum :
    TensorAlgebra R M ≃ₐ[R] TensorPowerSum (R := R) (M := M) :=
  TensorAlgebra.equivDirectSum

@[simp]
theorem ofTensorPowerSum_toTensorPowerSum (x : TensorAlgebra R M) :
    ofTensorPowerSum (toTensorPowerSum x) = x := by
  exact TensorAlgebra.ofDirectSum_toDirectSum x

@[simp]
theorem toTensorPowerSum_ofTensorPowerSum (x : TensorPowerSum (R := R) (M := M)) :
    toTensorPowerSum (ofTensorPowerSum x) = x := by
  exact TensorAlgebra.toDirectSum_ofDirectSum x

@[simp]
theorem toTensorPowerSum_include (x : M) :
    toTensorPowerSum (TensorAlgebra.ι R x) =
      DirectSum.of (fun n : ℕ => ⨂[R]^n M) 1 (PiTensorProduct.tprod R fun _ : Fin 1 => x) := by
  exact TensorAlgebra.toDirectSum_ι x

@[simp]
theorem ofTensorPowerSum_tprod {n : ℕ} (x : Fin n → M) :
    ofTensorPowerSum (DirectSum.of (fun n : ℕ => ⨂[R]^n M) n (PiTensorProduct.tprod R x)) =
      TensorAlgebra.tprod R M n x := by
  exact TensorAlgebra.ofDirectSum_of_tprod x

@[simp]
theorem toTensorPowerSum_tprod {n : ℕ} (x : Fin n → M) :
    toTensorPowerSum (TensorAlgebra.tprod R M n x) =
      DirectSum.of (fun n : ℕ => ⨂[R]^n M) n (PiTensorProduct.tprod R x) := by
  exact TensorAlgebra.toDirectSum_tensorPower_tprod x

@[simp]
theorem tensorPower_toTensorAlgebra_tprod {n : ℕ} (x : Fin n → M) :
    TensorPower.toTensorAlgebra (PiTensorProduct.tprod R x) = TensorAlgebra.tprod R M n x := by
  exact TensorPower.toTensorAlgebra_tprod x

@[simp]
theorem tensorPower_toTensorAlgebra_mul {i j : ℕ}
    (a : ⨂[R]^i M) (b : ⨂[R]^j M) :
    TensorPower.toTensorAlgebra
        (@GradedMonoid.GMul.mul ℕ (fun n : ℕ => ⨂[R]^n M) _ _ _ _ a b) =
      TensorPower.toTensorAlgebra a * TensorPower.toTensorAlgebra b := by
  exact TensorPower.toTensorAlgebra_gMul a b

end TensorPowers

variable {R M : Type*}
variable [CommSemiring R]
variable [AddCommMonoid M] [Module R M]

/--
Induction on a tensor algebra via its graded direct-sum decomposition.

This is the tensor-algebra analogue of the finite-stage/direct-limit induction
principles used elsewhere in the repository: prove the zero component, prove
all homogeneous direct-sum pieces, and close under addition.
-/
@[elab_as_elim]
theorem tensorAlgebra_induction_on_directSum {C : TensorAlgebra R M → Prop}
    (h_zero : C 0)
    (h_homogeneous : ∀ n : ℕ, ∀ x : ⨂[R]^n M,
      C (ofTensorPowerSum (DirectSum.of (fun n : ℕ => ⨂[R]^n M) n x)))
    (h_add : ∀ a b : TensorAlgebra R M, C a → C b → C (a + b))
    (a : TensorAlgebra R M) : C a := by
  rw [← ofTensorPowerSum_toTensorPowerSum a]
  refine DirectSum.induction_on (toTensorPowerSum a) ?_ ?_ ?_
  · simpa using h_zero
  · intro n x
    simpa using h_homogeneous n x
  · intro x y hx hy
    simpa using h_add (ofTensorPowerSum x) (ofTensorPowerSum y) hx hy

section QuotientAlgebras

variable {R M : Type*}
variable [CommRing R]
variable [AddCommGroup M] [Module R M]

abbrev EA : Type _ := ExteriorAlgebra R M

abbrev SA : Type _ := SymmetricAlgebra R M

end QuotientAlgebras

end TensorAlgebraCanonical
