import Mathlib.Algebra.Lie.Basic
import InfoGeometry.Canonical.SouriauKKSForm
import InfoGeometry.Canonical.SouriauContragredientPairing

/-!
# KKS transport under a bracket-preserving linear equivalence

This is the finite algebraic equivariance square between the adjoint action
on a Lie algebra, the contragredient action on its dual, and the KKS form.
It does not assert that the equivalence comes from a Lie group or construct a
coadjoint orbit.
-/

noncomputable section

namespace InfoGeometry.Canonical.SouriauKKSContragredientBridge

open SouriauKKS
open InfoGeometry.Canonical.SouriauContragredientPairing

variable {R L : Type*} [CommRing R] [LieRing L] [LieAlgebra R L]

theorem kksForm_contragredient_invariant
    (e : L ≃ₗ[R] L)
    (hLie : ∀ X Y : L, e ⁅X, Y⁆ = ⁅e X, e Y⁆)
    (μ : Module.Dual R L) (X Y : L) :
    kksForm (contragredient e μ) (e X) (e Y) =
      kksForm μ X Y := by
  unfold kksForm
  rw [← hLie X Y]
  exact contragredient_pairing_invariant e μ ⁅X, Y⁆

theorem affineKksForm_contragredient_invariant
    (e : L ≃ₗ[R] L)
    (hLie : ∀ X Y : L, e ⁅X, Y⁆ = ⁅e X, e Y⁆)
    (μ : Module.Dual R L) (θ : L →ₗ[R] L →ₗ[R] R)
    (hθ : ∀ X Y : L, θ (e X) (e Y) = θ X Y)
    (X Y : L) :
    affineKksForm (contragredient e μ) θ (e X) (e Y) =
      affineKksForm μ θ X Y := by
  unfold affineKksForm
  rw [kksForm_contragredient_invariant e hLie μ X Y, hθ]

end SouriauKKSContragredientBridge

end Canonical
