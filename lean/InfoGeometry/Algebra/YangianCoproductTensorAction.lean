import Mathlib.LinearAlgebra.TensorProduct.Basic
import InfoGeometry.Algebra.FiniteSpinAlgebra
import Mathlib.RingTheory.Coalgebra.Basic

/-!
# Coalgebra-compatible tensor actions

This owner isolates the exact algebraic contract needed before discussing a
Yangian gluing theorem.  It uses Mathlib's genuine `Coalgebra.comul` and
`Coalgebra.counit`, but it does not assert that an arbitrary coalgebra is a
Yangian, nor does it provide Serre relations or a level-one representation.

The tensor action is supplied together with its coproduct compatibility and
the action law on counital invariant pure tensors.  The latter is an explicit
representation property: it is not inferred from names or from a scalar
kernel argument.
-/

namespace InfoGeometry.Algebra

open TensorProduct

variable {R A V W : Type*}
variable [CommSemiring R] [Semiring A] [Module R A] [Coalgebra R A]
variable [AddCommMonoid V] [Module R V]
variable [AddCommMonoid W] [Module R W]

/-- Invariance of a vector under an operator at the coalgebra counit. -/
def IsCounitalInvariant
    (rho : A → Module.End R V) (a : A) (v : V) : Prop :=
  rho a v = ((Coalgebra.counit : A →ₗ[R] R) a) • v

/--
An explicit tensor-product action compatible with a coalgebra coproduct.

`coproductAction` evaluates elements of `A ⊗ A` on `V ⊗ W`; the compatibility
field ties the generator action to the actual Mathlib coproduct.  The final
field records the counital tensor law on pure tensors.
-/
structure YangianCoproductTensorAction where
  rhoV : A → Module.End R V
  rhoW : A → Module.End R W
  rhoTensor : A → Module.End R (TensorProduct R V W)
  coproductAction :
    (TensorProduct R A A) →ₗ[R] Module.End R (TensorProduct R V W)
  coproduct_compatibility :
    ∀ a : A,
      rhoTensor a =
        coproductAction ((Coalgebra.comul : A →ₗ[R] TensorProduct R A A) a)
  counital_tensor_rule :
    ∀ (a : A) (v : V) (w : W),
      IsCounitalInvariant rhoV a v →
      IsCounitalInvariant rhoW a w →
      IsCounitalInvariant rhoTensor a (v ⊗ₜ[R] w)

theorem coproduct_tensor_action_compatible
    (T : YangianCoproductTensorAction (R := R) (A := A) (V := V) (W := W))
    (a : A) :
    T.rhoTensor a =
      T.coproductAction ((Coalgebra.comul : A →ₗ[R] TensorProduct R A A) a) :=
  T.coproduct_compatibility a

theorem tensor_counital_invariant
    (T : YangianCoproductTensorAction (R := R) (A := A) (V := V) (W := W))
    (a : A) (v : V) (w : W)
    (hv : IsCounitalInvariant T.rhoV a v)
    (hw : IsCounitalInvariant T.rhoW a w) :
    IsCounitalInvariant T.rhoTensor a (v ⊗ₜ[R] w) :=
  T.counital_tensor_rule a v w hv hw

theorem tensor_annihilated_of_zero_counit
    (T : YangianCoproductTensorAction (R := R) (A := A) (V := V) (W := W))
    (a : A) (v : V) (w : W)
    (hc : (Coalgebra.counit : A →ₗ[R] R) a = 0)
    (hv : T.rhoV a v = 0)
    (hw : T.rhoW a w = 0) :
    T.rhoTensor a (v ⊗ₜ[R] w) = 0 := by
  have hvi : IsCounitalInvariant T.rhoV a v := by
    unfold IsCounitalInvariant
    rw [hc, zero_smul]
    exact hv
  have hwi : IsCounitalInvariant T.rhoW a w := by
    unfold IsCounitalInvariant
    rw [hc, zero_smul]
    exact hw
  have htensor := tensor_counital_invariant T a v w hvi hwi
  unfold IsCounitalInvariant at htensor
  rw [hc, zero_smul] at htensor
  exact htensor

end InfoGeometry.Algebra
