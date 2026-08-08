import Mathlib.RingTheory.HopfAlgebra.Basic
import Mathlib.RingTheory.Coalgebra.Convolution

/-!
# Convolution characterization and uniqueness of the antipode

Mathlib supplies the two antipode identities as equalities of linear maps.
This module derives their standard convolution-algebra formulation and proves
uniqueness of an antipode on a bialgebra.
-/

namespace InfoGeometry.Algebra.HopfConvolution

open Coalgebra HopfAlgebra LinearMap WithConv

universe u v

/-- The antipode is a right convolution inverse of the identity map. -/
theorem antipode_conv_id
    {R : Type u} {A : Type v}
    [CommSemiring R] [Semiring A] [HopfAlgebra R A] :
    (toConv (HopfAlgebra.antipode R) : WithConv (A →ₗ[R] A)) *
        toConv LinearMap.id = 1 := by
  ext a
  simp [convMul_apply, convOne_apply]
  exact HopfAlgebra.mul_antipode_rTensor_comul_apply a

/-- The antipode is a left convolution inverse of the identity map. -/
theorem id_conv_antipode
    {R : Type u} {A : Type v}
    [CommSemiring R] [Semiring A] [HopfAlgebra R A] :
    (toConv (LinearMap.id : A →ₗ[R] A)) *
        toConv (HopfAlgebra.antipode R) = 1 := by
  ext a
  simp [convMul_apply, convOne_apply]
  exact HopfAlgebra.mul_antipode_lTensor_comul_apply a

/--
An antipode on a bialgebra is unique: a right convolution inverse and a left
convolution inverse of the identity linear map coincide.
-/
theorem antipode_unique
    {R : Type u} {A : Type v}
    [CommSemiring R] [Semiring A] [Bialgebra R A]
    (S₁ S₂ : A →ₗ[R] A)
    (hS₁ :
      LinearMap.mul' R A ∘ₗ S₁.rTensor A ∘ₗ Coalgebra.comul =
        Algebra.linearMap R A ∘ₗ Coalgebra.counit)
    (hS₂ :
      LinearMap.mul' R A ∘ₗ S₂.lTensor A ∘ₗ Coalgebra.comul =
        Algebra.linearMap R A ∘ₗ Coalgebra.counit) :
    S₁ = S₂ := by
  have hright :
      (toConv S₁ : WithConv (A →ₗ[R] A)) *
          toConv LinearMap.id = 1 := by
    ext a
    simp [convMul_apply, convOne_apply]
    exact LinearMap.congr_fun hS₁ a
  have hleft :
      (toConv (LinearMap.id : A →ₗ[R] A)) *
          toConv S₂ = 1 := by
    ext a
    simp [convMul_apply, convOne_apply]
    exact LinearMap.congr_fun hS₂ a
  have hconv : (toConv S₁ : WithConv (A →ₗ[R] A)) = toConv S₂ :=
    calc
      toConv S₁ = toConv S₁ * 1 := (mul_one _).symm
      _ = toConv S₁ * (toConv LinearMap.id * toConv S₂) := by rw [hleft]
      _ = (toConv S₁ * toConv LinearMap.id) * toConv S₂ := (mul_assoc _ _ _).symm
      _ = 1 * toConv S₂ := by rw [hright]
      _ = toConv S₂ := one_mul _
  exact toConv_injective hconv

/--
Conjugation by a unit fixes an element exactly when that element commutes with
the unit.  This elementary ring lemma is the algebraic content needed when an
antipode-square formula is known to be inner.
-/
theorem conjugate_eq_self_iff_commute
    {A : Type v} [Semiring A] (u : Aˣ) (x : A) :
    (u : A) * x * (↑(u⁻¹) : A) = x ↔
      (u : A) * x = x * (u : A) := by
  constructor
  · intro hfix
    calc
      (u : A) * x =
          ((u : A) * x * (↑(u⁻¹) : A)) * (u : A) := by
            simp [mul_assoc]
      _ = x * (u : A) := by rw [hfix]
  · intro hcomm
    calc
      (u : A) * x * (↑(u⁻¹) : A) =
          x * (u : A) * (↑(u⁻¹) : A) := by rw [hcomm]
      _ = x := by simp [mul_assoc]

/--
If the square of the Hopf antipode is implemented by conjugation by a unit
`u`, then its fixed elements are exactly the elements commuting with `u`.

The innerness property is explicit: it is not a consequence of
`HopfAlgebra R A` alone.
-/
theorem antipode_sq_eq_self_iff_commute_of_conjugation
    {R : Type u} {A : Type v}
    [CommSemiring R] [Semiring A] [HopfAlgebra R A]
    (u : Aˣ)
    (hconj : ∀ x : A,
      HopfAlgebra.antipode R (HopfAlgebra.antipode R x) =
        (u : A) * x * (↑(u⁻¹) : A))
    (x : A) :
    HopfAlgebra.antipode R (HopfAlgebra.antipode R x) = x ↔
      (u : A) * x = x * (u : A) := by
  rw [hconj]
  exact conjugate_eq_self_iff_commute u x

/--
If an inner implementer of the antipode square acts noncentrally on `x`, then
the antipode is not involutive on `x`.

No implication from entropy production or from `HopfAlgebra R A` alone is
used; the inner-implementation law and the noncommutation property are explicit.
-/
theorem antipode_sq_ne_self_of_not_commute_of_conjugation
    {R : Type u} {A : Type v}
    [CommSemiring R] [Semiring A] [HopfAlgebra R A]
    (u : Aˣ)
    (hconj : ∀ x : A,
      HopfAlgebra.antipode R (HopfAlgebra.antipode R x) =
        (u : A) * x * (↑(u⁻¹) : A))
    (x : A)
    (hnoncomm : (u : A) * x ≠ x * (u : A)) :
    HopfAlgebra.antipode R (HopfAlgebra.antipode R x) ≠ x := by
  intro hfix
  exact hnoncomm
    ((antipode_sq_eq_self_iff_commute_of_conjugation u hconj x).mp hfix)

/--
A noncentral inner implementer supplies an explicit property that the antipode
square is not the identity.
-/
theorem exists_antipode_sq_ne_self_of_exists_not_commute
    {R : Type u} {A : Type v}
    [CommSemiring R] [Semiring A] [HopfAlgebra R A]
    (u : Aˣ)
    (hconj : ∀ x : A,
      HopfAlgebra.antipode R (HopfAlgebra.antipode R x) =
        (u : A) * x * (↑(u⁻¹) : A))
    (hnoncentral : ∃ x : A, (u : A) * x ≠ x * (u : A)) :
    ∃ x : A, HopfAlgebra.antipode R (HopfAlgebra.antipode R x) ≠ x := by
  rcases hnoncentral with ⟨x, hx⟩
  exact ⟨x, antipode_sq_ne_self_of_not_commute_of_conjugation u hconj x hx⟩

end InfoGeometry.Algebra.HopfConvolution
