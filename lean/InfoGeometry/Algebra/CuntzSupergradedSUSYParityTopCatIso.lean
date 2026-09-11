import InfoGeometry.Algebra.CuntzSupergradedSUSYTopological
import InfoGeometry.Algebra.FiniteSpinAlgebra

/-!
# Topological isomorphism of the supergraded parity

The realization owner already supplies a continuous involutive algebra
equivalence.  This file exposes that same equivalence as Mathlib's native
`ContinuousAlgEquiv` and as an isomorphism in `TopCat`.
-/

noncomputable section

namespace InfoGeometry.Algebra.SupergradedSUSY.Topological

open CategoryTheory

universe u

variable {B : Type u} [CStarAlgebra B]

private theorem parity_symm_eq (R : Realization (B := B) n)
    (h_involutive : ∀ x : B, R.parity (R.parity x) = x) :
    R.parity.symm = R.parity := by
  ext x
  apply R.parity.injective
  rw [R.parity.apply_symm_apply, h_involutive]

/-- The continuous algebra equivalence underlying the parity involution. -/
def parityContinuousAlgEquiv (R : Realization (B := B) n)
    (h_cont : Continuous R.parity)
    (h_involutive : ∀ x : B, R.parity (R.parity x) = x) :
    B ≃A[ℂ] B :=
  ContinuousAlgEquiv.mk R.parity h_cont (by
    simpa [parity_symm_eq R h_involutive] using h_cont)

@[simp] theorem parityContinuousAlgEquiv_apply
    (R : Realization (B := B) n) (h_cont : Continuous R.parity)
    (h_involutive : ∀ x : B, R.parity (R.parity x) = x) (x : B) :
    parityContinuousAlgEquiv R h_cont h_involutive x = R.parity x :=
  rfl

@[simp] theorem parityContinuousAlgEquiv_symm_apply
    (R : Realization (B := B) n) (h_cont : Continuous R.parity)
    (h_involutive : ∀ x : B, R.parity (R.parity x) = x) (x : B) :
    (parityContinuousAlgEquiv R h_cont h_involutive).symm x = R.parity x := by
  change R.parity.symm x = R.parity x
  rw [parity_symm_eq R h_involutive]

def parityTopCatIso (R : Realization (B := B) n)
    (h_cont : Continuous R.parity)
    (h_involutive : ∀ x : B, R.parity (R.parity x) = x) :
    TopCat.of B ≅ TopCat.of B where
  hom := TopCat.ofHom
    { toFun := R.parity
      continuous_toFun := h_cont }
  inv := TopCat.ofHom
    { toFun := R.parity
      continuous_toFun := h_cont }
  hom_inv_id := by
    apply TopCat.hom_ext
    ext x
    rw [TopCat.comp_app, TopCat.id_app]
    exact h_involutive x
  inv_hom_id := by
    apply TopCat.hom_ext
    ext x
    rw [TopCat.comp_app, TopCat.id_app]
    exact h_involutive x

@[simp] theorem parityTopCatIso_hom_apply
    (R : Realization (B := B) n) (h_cont : Continuous R.parity)
    (h_involutive : ∀ x : B, R.parity (R.parity x) = x) (x : B) :
    (parityTopCatIso R h_cont h_involutive).hom x = R.parity x :=
  rfl

@[simp] theorem parityTopCatIso_inv_apply
    (R : Realization (B := B) n) (h_cont : Continuous R.parity)
    (h_involutive : ∀ x : B, R.parity (R.parity x) = x) (x : B) :
    (parityTopCatIso R h_cont h_involutive).inv x = R.parity x :=
  rfl

theorem parityTopCatIso_hom_eq_endomorphism
    (R : Realization (B := B) n) (h_cont : Continuous R.parity)
    (h_involutive : ∀ x : B, R.parity (R.parity x) = x) :
    (parityTopCatIso R h_cont h_involutive).hom =
      parityTopCatEndomorphism (n := n) R h_cont := by
  rfl

end InfoGeometry.Algebra.SupergradedSUSY.Topological
