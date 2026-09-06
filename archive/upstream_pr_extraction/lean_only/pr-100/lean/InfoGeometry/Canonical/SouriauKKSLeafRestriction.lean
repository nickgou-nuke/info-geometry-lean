import InfoGeometry.Canonical.SouriauKKSForm
import Mathlib.Algebra.Lie.Subalgebra

/-!
# Restricted algebraic KKS forms

This owner contains only the native algebraic restriction of the KKS pairing
to a Lie subalgebra.  It does not identify that subalgebra with a smooth orbit
or assert non-degeneracy without an explicit hypothesis.
-/

namespace InfoGeometry.Canonical

open SouriauKKS

noncomputable section

variable {R L : Type*} [CommRing R] [LieRing L] [LieAlgebra R L]

def kksRestriction (μ : Module.Dual R L) (S : LieSubalgebra R L) :
    S →ₗ[R] S →ₗ[R] R :=
  LinearMap.mk₂ R
    (fun X Y => kksForm μ (X : L) (Y : L))
    (by intro X₁ X₂ Y; exact kksForm_add_left μ (X₁ : L) (X₂ : L) (Y : L))
    (by intro a X Y; exact kksForm_smul_left μ a (X : L) (Y : L))
    (by intro X Y₁ Y₂; exact kksForm_add_right μ (X : L) (Y₁ : L) (Y₂ : L))
    (by intro a X Y; exact kksForm_smul_right μ a (X : L) (Y : L))

theorem kksRestriction_apply (μ : Module.Dual R L) (S : LieSubalgebra R L)
    (X Y : S) :
    kksRestriction μ S X Y = kksForm μ (X : L) (Y : L) := rfl

theorem kksRestriction_skew (μ : Module.Dual R L) (S : LieSubalgebra R L)
    (X Y : S) :
    kksRestriction μ S X Y = -kksRestriction μ S Y X := by
  rw [kksRestriction_apply, kksRestriction_apply, kksForm_skew]

theorem kksRestriction_closed (μ : Module.Dual R L) (S : LieSubalgebra R L)
    (X Y Z : S) :
    kksRestriction μ S X (⟨⁅(Y : L), (Z : L)⁆, S.lie_mem' Y.property Z.property⟩ : S) +
      kksRestriction μ S Y (⟨⁅(Z : L), (X : L)⁆, S.lie_mem' Z.property X.property⟩ : S) +
      kksRestriction μ S Z (⟨⁅(X : L), (Y : L)⁆, S.lie_mem' X.property Y.property⟩ : S) = 0 := by
  rw [kksRestriction_apply, kksRestriction_apply, kksRestriction_apply]
  exact kksForm_jacobi μ (X : L) (Y : L) (Z : L)

theorem kksRestriction_nondegenerate
    (μ : Module.Dual R L) (S : LieSubalgebra R L)
    (h : ∀ X : L, X ∈ S →
      (∀ Y : L, Y ∈ S → kksForm μ X Y = 0) → X = 0) :
    ∀ X : S, (∀ Y : S, kksRestriction μ S X Y = 0) → X = 0 := by
  intro X hX
  apply Subtype.ext
  apply h (X : L) X.property
  intro Y hY
  have hY' : (⟨Y, hY⟩ : S) = ⟨Y, hY⟩ := rfl
  have := hX (⟨Y, hY⟩ : S)
  simpa [kksRestriction_apply] using this

end
end InfoGeometry.Canonical
