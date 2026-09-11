import Mathlib
import InfoGeometry.Algebra.FiniteSpinAlgebra

/-! Transport of a bilinear product and Leibniz operators across a linear
equivalence.  This is the algebraic core used by the H3/Zorn soldering
frontier; no particular coordinate model is assumed here.
-/

namespace InfoGeometry.Canonical

structure AlgebraicSoldering (R A B : Type*)
    [Semiring R] [AddCommMonoid A] [Module R A]
    [AddCommMonoid B] [Module R B] where
  equiv : A ≃ₗ[R] B
  sourceMul : A → A → A
  targetMul : B → B → B
  map_mul : ∀ x y, equiv (sourceMul x y) = targetMul (equiv x) (equiv y)

namespace AlgebraicSoldering

variable {R A B : Type*} [Semiring R]
  [AddCommMonoid A] [Module R A] [AddCommMonoid B] [Module R B]

def transport (S : AlgebraicSoldering R A B) (D : A →ₗ[R] A) : B →ₗ[R] B :=
  S.equiv.toLinearMap.comp (D.comp S.equiv.symm.toLinearMap)

@[simp] theorem transport_apply (S : AlgebraicSoldering R A B)
    (D : A →ₗ[R] A) (x : B) : S.transport D x = S.equiv (D (S.equiv.symm x)) := rfl

theorem transport_preserves_leibniz (S : AlgebraicSoldering R A B)
    (D : A →ₗ[R] A)
    (hD : ∀ x y, D (S.sourceMul x y) =
      S.sourceMul (D x) y + S.sourceMul x (D y)) :
    ∀ x y, S.transport D (S.targetMul x y) =
      S.targetMul (S.transport D x) y + S.targetMul x (S.transport D y) := by
  intro x y
  rw [transport_apply]
  have hxy : S.equiv.symm (S.targetMul x y) =
      S.sourceMul (S.equiv.symm x) (S.equiv.symm y) := by
    apply S.equiv.injective
    simpa only [S.equiv.apply_symm_apply] using
      (S.map_mul (S.equiv.symm x) (S.equiv.symm y)).symm
  rw [hxy, hD, map_add, S.map_mul, S.map_mul]
  simp only [S.equiv.apply_symm_apply, transport_apply]

theorem transport_reflects_leibniz (S : AlgebraicSoldering R A B)
    (D : A →ₗ[R] A)
    (hD : ∀ x y, S.transport D (S.targetMul x y) =
      S.targetMul (S.transport D x) y + S.targetMul x (S.transport D y)) :
    ∀ x y, D (S.sourceMul x y) =
      S.sourceMul (D x) y + S.sourceMul x (D y) := by
  intro x y
  apply S.equiv.injective
  have hxy : S.equiv.symm (S.targetMul (S.equiv x) (S.equiv y)) =
      S.sourceMul x y := by
    apply S.equiv.injective
    simpa only [S.equiv.apply_symm_apply] using (S.map_mul x y).symm
  have h := hD (S.equiv x) (S.equiv y)
  change S.equiv (D (S.equiv.symm
      (S.targetMul (S.equiv x) (S.equiv y)))) = _ at h
  rw [hxy] at h
  simp only [transport_apply, S.equiv.apply_symm_apply] at h
  simp only [transport_apply, S.equiv.symm_apply_apply] at h
  rw [← S.map_mul, ← S.map_mul, ← map_add] at h
  exact h

end AlgebraicSoldering
end InfoGeometry.Canonical
