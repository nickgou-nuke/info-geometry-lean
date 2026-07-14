import InfoGeometry.Dynamics.KanDecomposition
import InfoGeometry.Jordan.BurgStein
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Tactic

noncomputable section

/-!
# LogDetBarrier

Two-dimensional log-determinant barrier adapter for the parabolic `N` lane of
the KAN/Bregman bridge.

The repo already contains the real SPD determinant-divergence layer in
`InfoGeometry.Jordan.LogDet` and `InfoGeometry.Jordan.BurgStein`.  This file
adds the exact complex `2 × 2` facts used by the LCFT / optimal-transport
envelope:

* `componentN t` has determinant `1`;
* therefore the determinant-only logarithmic barrier sees `N` as
  volume-preserving;
* congruence by `N`, `X ↦ N X Nᴴ`, preserves determinant because
  `det N = 1`.

This is deliberately the finite algebraic log-det shadow, not a full
self-concordance theorem for matrix cones.
-/

namespace LogDetBarrier

open Matrix
open InfoGeometry.Dynamics.KanDecomposition

/-- The `2 × 2` complex matrix carrier used by the KAN/parabolic bridge. -/
abbrev Mat2C := Matrix (Fin 2) (Fin 2) ℂ

/--
Determinant-only logarithmic barrier on complex `2 × 2` matrices, using the
norm of the determinant as the positive scalar readout.
-/
def logAbsDetBarrier2 (X : Mat2C) : ℝ :=
  -Real.log ‖X.det‖

/--
Burg/log-det readout from the identity:
`tr X - log |det X| - 2`.

For the unipotent `N` lane this vanishes exactly: the trace and determinant are
both the identity readouts.
-/
def logDetBurgFromIdentity2 (X : Mat2C) : ℝ :=
  (Matrix.trace X).re - 2 - Real.log ‖X.det‖

/-- Congruence action by the parabolic `N` component. -/
def componentNCongruence (t : ℂ) (X : Mat2C) : Mat2C :=
  componentN t * X * (componentN t)ᴴ

/-! ## Determinant and trace readouts for the `N` lane -/

/-- The parabolic `N` component lies in the determinant-one sector. -/
theorem componentN_det_eq_one (t : ℂ) :
    (componentN t).det = 1 := by
  rw [componentN_eq]
  simp [Matrix.det_fin_two]

/-- The parabolic `N` component is invertible by determinant. -/
theorem componentN_det_ne_zero (t : ℂ) :
    (componentN t).det ≠ 0 := by
  simp [componentN_det_eq_one]

/-- The trace of the unipotent `N` component is the identity trace `2`. -/
theorem componentN_trace_eq_two (t : ℂ) :
    Matrix.trace (componentN t) = 2 := by
  rw [componentN_eq]
  norm_num [Matrix.trace_fin_two]

/-- The determinant-only log barrier vanishes on the parabolic `N` lane. -/
theorem logAbsDetBarrier2_componentN_eq_zero (t : ℂ) :
    logAbsDetBarrier2 (componentN t) = 0 := by
  simp [logAbsDetBarrier2, componentN_det_eq_one]

/--
The trace-logdet Burg readout from the identity also vanishes on `N(t)`.
This is the exact finite-dimensional version of “pure nilpotent shear changes
the natural parameter but not the determinant volume”.
-/
theorem logDetBurgFromIdentity2_componentN_eq_zero (t : ℂ) :
    logDetBurgFromIdentity2 (componentN t) = 0 := by
  simp [logDetBurgFromIdentity2, componentN_trace_eq_two, componentN_det_eq_one]

/-! ## Determinant preservation under the parabolic congruence -/

/--
Congruence by the parabolic `N` component preserves determinants:
`det (N X Nᴴ) = det X`.

This is the finite matrix statement behind the log-det volume invariance of
the unipotent radical.
-/
theorem componentNCongruence_det (t : ℂ) (X : Mat2C) :
    (componentNCongruence t X).det = X.det := by
  unfold componentNCongruence
  rw [Matrix.det_mul, Matrix.det_mul, componentN_det_eq_one,
    Matrix.det_conjTranspose]
  simp [componentN_det_eq_one]

/-- The determinant-only barrier is invariant under parabolic congruence. -/
theorem logAbsDetBarrier2_componentNCongruence (t : ℂ) (X : Mat2C) :
    logAbsDetBarrier2 (componentNCongruence t X) =
      logAbsDetBarrier2 X := by
  simp [logAbsDetBarrier2, componentNCongruence_det]

/--
The determinant part of Burg/Stein divergence is unchanged by parabolic
congruence.  This is the algebraic kernel used by the log-det barrier adapter.
-/
theorem log_det_norm_componentNCongruence (t : ℂ) (X : Mat2C) :
    Real.log ‖(componentNCongruence t X).det‖ =
      Real.log ‖X.det‖ := by
  simp [componentNCongruence_det]

end LogDetBarrier
