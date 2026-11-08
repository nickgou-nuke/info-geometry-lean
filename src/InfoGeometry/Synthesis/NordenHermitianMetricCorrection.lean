/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.Synthesis.CategoricalInevitabilityPosetSynthesis

/-!
# The Hermitian form associated with a para-Kähler sheet swap

The para-Kähler metric `g` is anti-invariant under the induced complex structure
`J = C ∘ K`. Given a `g`-isometric involutive sheet swap `C`, the form
`g_C(v,w) = g(v,Cw)` is symmetric and `J`-invariant. With the repository's
convention `ω(v,w) = g(v,Kw)`, its fundamental form is `-ω` (the sign matters).
This is an algebraic Hermitian-form statement; nondegeneracy and
differential-geometric Kähler conditions are not assumed here.
-/

set_option autoImplicit false

namespace InfoGeometry.Synthesis.NordenHermitianMetricCorrection

open InfoGeometry.Canonical.SuperGrassmannianManifold
open InfoGeometry.Canonical.ParaKahlerLagrangianDimension
open InfoGeometry.Synthesis.CategoricalInevitabilityPosetSynthesis

variable {V : Type*} [AddCommGroup V] [Module ℝ V]

/-- The symmetric-form candidate obtained by composing the second argument with
the `g`-isometric sheet swap `C`. -/
def inducedJHermitianForm
    (g : V →ₗ[ℝ] V →ₗ[ℝ] ℝ) (C : V →ₗ[ℝ] V) (v w : V) : ℝ :=
  g v (C w)

/-- The induced form is symmetric when `g` is symmetric and `C` is an isometric
involution. -/
theorem inducedJHermitianForm_symmetric
    (g omega : V →ₗ[ℝ] V →ₗ[ℝ] ℝ) (K C : V →ₗ[ℝ] V)
    (hPK : ParaKahlerStructure g omega K)
    (hC : IsSheetSwapInvolution K C)
    (hC_iso : ∀ u w, g (C u) (C w) = g u w) (v w : V) :
    inducedJHermitianForm g C v w = inducedJHermitianForm g C w v := by
  calc
    g v (C w) = g (C w) v := hPK.g_symm v (C w)
    _ = g (C w) (C (C v)) := by rw [sheetSwapInvolution_apply_sq K C hC v]
    _ = g w (C v) := hC_iso w (C v)

/-- Nondegeneracy transfers from `g` to the induced form because the sheet swap
is surjective (indeed involutive). -/
theorem inducedJHermitianForm_nondegenerate
    (g : V →ₗ[ℝ] V →ₗ[ℝ] ℝ) (K C : V →ₗ[ℝ] V)
    (hC : IsSheetSwapInvolution K C)
    (hnd : ∀ v, (∀ w, g v w = 0) → v = 0) :
    ∀ v, (∀ w, inducedJHermitianForm g C v w = 0) → v = 0 := by
  intro v hv
  apply hnd v
  intro w
  have h := hv (C w)
  change g v (C (C w)) = 0 at h
  rw [sheetSwapInvolution_apply_sq K C hC w] at h
  exact h

/-- The induced form is invariant under `J = C ∘ K`; this is the Hermitian
sign, complementary to the anti-invariance of the original para-Kähler metric. -/
theorem inducedJHermitianForm_J_invariant
    (g omega : V →ₗ[ℝ] V →ₗ[ℝ] ℝ) (K C : V →ₗ[ℝ] V)
    (hK : ParaComplexStructure K)
    (hPK : ParaKahlerStructure g omega K)
    (hC : IsSheetSwapInvolution K C)
    (hC_iso : ∀ u w, g (C u) (C w) = g u w) (v w : V) :
    inducedJHermitianForm g C (inducedComplexStructure C K v)
        (inducedComplexStructure C K w) = inducedJHermitianForm g C v w := by
  have hCK : C (K w) = -K (C w) := by
    have h := mobiusTwist_apply_comm K C hC.2 w
    exact (neg_eq_iff_eq_neg.mpr h).symm
  change g (C (K v)) (C (C (K w))) = g v (C w)
  calc
    g (C (K v)) (C (C (K w))) = g (K v) (C (K w)) := hC_iso (K v) (C (K w))
    _ = g (K v) (-K (C w)) := by rw [hCK]
    _ = -g (K v) (K (C w)) := by simp only [map_neg]
    _ = g v (C w) := by rw [metric_anti_invariance g omega K hK hPK v (C w)]; ring

/-- Under the repository convention `ω(v,w) = g(v,Kw)`, the fundamental form
of `g_C` and `J` is `-ω`. -/
theorem inducedJHermitianForm_fundamental_form
    (g omega : V →ₗ[ℝ] V →ₗ[ℝ] ℝ) (K C : V →ₗ[ℝ] V)
    (hPK : ParaKahlerStructure g omega K)
    (hC_iso : ∀ u w, g (C u) (C w) = g u w) (v w : V) :
    inducedJHermitianForm g C (inducedComplexStructure C K v) w = -omega v w := by
  change g (C (K v)) (C w) = -omega v w
  calc
    g (C (K v)) (C w) = g (K v) w := hC_iso (K v) w
    _ = omega (K v) (K w) := hPK.compatibility (K v) w
    _ = -omega v w := hPK.omega_anti_inv v w

end InfoGeometry.Synthesis.NordenHermitianMetricCorrection
