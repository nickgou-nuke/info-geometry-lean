import Mathlib.RingTheory.Coalgebra.Basic
import InfoGeometry.Algebra.FiniteSpinAlgebra

/-!
# Comodules over a mathlib coalgebra

This is the theorem-clean part of Definition 1.20.2 from the Atlas tensor
category development, separated from the later Tannakian reconstruction
results in that external module.  The underlying coalgebra, tensor product,
coassociativity, and counit laws are mathlib owners.
-/

namespace InfoGeometry.Algebra.Coalgebra

open scoped TensorProduct

universe u v w

/-- A left comodule over a mathlib coalgebra. -/
class LeftComodule
    (R : Type u) (C : Type v) (M : Type w)
    [CommSemiring R]
    [AddCommMonoid C] [Module R C] [Coalgebra R C]
    [AddCommMonoid M] [Module R M] where
  coact : M →ₗ[R] C ⊗[R] M
  coassoc :
    TensorProduct.assoc R C C M ∘ₗ
        Coalgebra.comul.rTensor M ∘ₗ coact =
      coact.lTensor C ∘ₗ coact
  counit_coact :
    Coalgebra.counit.rTensor M ∘ₗ coact =
      TensorProduct.mk R R M 1

/-- A right comodule over a mathlib coalgebra. -/
class RightComodule
    (R : Type u) (C : Type v) (M : Type w)
    [CommSemiring R]
    [AddCommMonoid C] [Module R C] [Coalgebra R C]
    [AddCommMonoid M] [Module R M] where
  coact : M →ₗ[R] M ⊗[R] C
  coassoc :
    TensorProduct.assoc R M C C ∘ₗ
        coact.rTensor C ∘ₗ coact =
      Coalgebra.comul.lTensor M ∘ₗ coact
  counit_coact :
    Coalgebra.counit.lTensor M ∘ₗ coact =
      (TensorProduct.mk R M R).flip 1

/--
Every coalgebra is canonically a left comodule over itself.  The proof is
exactly mathlib coalgebra coassociativity and the right counit law.
-/
instance instLeftComoduleRegular
    (R : Type u) (C : Type v)
    [CommSemiring R]
    [AddCommMonoid C] [Module R C] [Coalgebra R C] :
    LeftComodule R C C where
  coact := Coalgebra.comul
  coassoc := Coalgebra.coassoc
  counit_coact := Coalgebra.rTensor_counit_comp_comul

/--
Every coalgebra is canonically a right comodule over itself.  The proof is
exactly mathlib coalgebra coassociativity and the left counit law.
-/
instance instRightComoduleRegular
    (R : Type u) (C : Type v)
    [CommSemiring R]
    [AddCommMonoid C] [Module R C] [Coalgebra R C] :
    RightComodule R C C where
  coact := Coalgebra.comul
  coassoc := Coalgebra.coassoc
  counit_coact := Coalgebra.lTensor_counit_comp_comul

end InfoGeometry.Algebra.Coalgebra
