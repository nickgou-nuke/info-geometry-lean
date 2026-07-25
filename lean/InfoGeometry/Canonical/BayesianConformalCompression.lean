import Mathlib.Tactic
import InfoGeometry.Algebra.HypercomplexTriad
import InfoGeometry.Canonical.ModularTensorInduction
import InfoGeometry.Canonical.ModularSL2R
import InfoGeometry.Canonical.DrazinAnomalousProjector

/-!
# InfoGeometry.Canonical.BayesianConformalCompression

Finite conformal compression on the `M₂(ℝ)` seed.

This file proves two concrete facts:
1. The Weyl-rescaled modular step has unit `(0,0)` diagonal entry.
2. The same step remains boundary-orthogonal against `N`.

No wrappers. No `sorry`.
-/

namespace InfoGeometry.Canonical.BayesianConformalCompression

open Matrix
open InfoGeometry.Algebra.HypercomplexTriad
open InfoGeometry.Canonical.ModularTensorInduction
open InfoGeometry.Canonical.ModularSL2R
open InfoGeometry.Canonical.DrazinAnomalousProjector

abbrev M2R := Matrix (Fin 2) (Fin 2) ℝ

/-- Weyl-rescaled finite modular step. -/
noncomputable def BayesianConformalUpdate (t : ℝ) : M2R :=
  Real.exp (-t) • expKExact t

/-- The primary diagonal channel is exactly normalized. -/
theorem bayesian_diagonal_compression (t : ℝ) :
    (BayesianConformalUpdate t) 0 0 = 1 := by
  unfold BayesianConformalUpdate
  rw [expKExact_eval]
  simp [Matrix.smul_apply]
  rw [← Real.exp_add]
  ring_nf
  simp

/-- Boundary pairing stays zero under conformal update. -/
theorem trace_conformal_update_boundary_invariant (t : ℝ) :
    traceForm (BayesianConformalUpdate t) N = 0 := by
  unfold BayesianConformalUpdate traceForm tr
  rw [expKExact_eval]
  norm_num [N, Matrix.mul_apply, Fin.sum_univ_two]

end InfoGeometry.Canonical.BayesianConformalCompression
