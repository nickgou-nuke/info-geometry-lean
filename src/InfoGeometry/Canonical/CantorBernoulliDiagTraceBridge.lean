/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/

import Mathlib.Tactic
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Integral.Bochner.SumMeasure
import InfoGeometry.Algebra.FiniteSpinAlgebra
import InfoGeometry.Canonical.CantorKMSState
import InfoGeometry.Canonical.UHFInductiveLimitBoundary
import InfoGeometry.Canonical.UHFInductiveColimitBoundaryTopology
import InfoGeometry.Canonical.CantorProjectiveBernoulliMeasure

/-!
# Finite diagonal trace and Bernoulli cylinder mass

This is a finite consumer bridge only.  It identifies cylinder-indicator trace
values with Bernoulli cylinder masses and proves that every finite-prefix
observable integrates to its normalized diagonal trace.  It does not construct
a positive functional on the full Cuntz `C*`-algebra or assert a KMS/GNS theorem.
-/

noncomputable section

namespace InfoGeometry.Canonical.CantorBernoulliDiagTraceBridge

open scoped ENNReal
open MeasureTheory
open InfoGeometry.Canonical.UHFInductiveColimitBoundary
open InfoGeometry.Canonical.UHFInductiveColimitBoundaryTopology
open InfoGeometry.Canonical.CantorKMSState
open InfoGeometry.Canonical.CantorProjectiveBernoulliMeasure
open InfoGeometry.Canonical.CantorProjectiveLimit
open InfoGeometry.Canonical.CantorProjectiveLimit.PrefixProjectiveLimit
open InfoGeometry.Analysis.FractalMeasure.Basic

theorem stageTrace_eq_DiagTrace (n : ℕ) (f : DiagAlg n) :
    InfoGeometry.Canonical.UHFInductiveLimitBoundary.stageTrace n f =
      DiagTrace n f := by
  unfold InfoGeometry.Canonical.UHFInductiveLimitBoundary.stageTrace DiagTrace
  rw [← inv_pow]

theorem diagTrace_cylinderIndicator_eq_projectivePrefixFiber_toReal
    (n : ℕ) (w : BitWord n) :
    DiagTrace n (cylinderIndicator n w) =
      ((projectiveLimitMeasure
          {q : PrefixProjectiveLimit |
            π n q = w}).toReal : ℂ) := by
  rw [DiagTrace_cylinderIndicator,
    projectiveLimitMeasure_apply_prefix_fiber]
  norm_num [ENNReal.toReal_ofNat]

/-- The projective-limit measure integrates every finite-prefix observable by
the normalized diagonal trace at that stage. -/
theorem projectiveLimitMeasure_integral_prefix_eq_DiagTrace
    (n : ℕ) (f : DiagAlg n) :
    ∫ q, f (π n q) ∂projectiveLimitMeasure = DiagTrace n f := by
  let ν : Measure (BitWord n) := Measure.map (π n) projectiveLimitMeasure
  have hν : IsFiniteMeasure ν := by
    dsimp [ν]
    infer_instance
  have hf : Integrable f ν := Integrable.of_finite
  rw [← integral_map (continuous_π n).measurable.aemeasurable
    hf.aestronglyMeasurable]
  rw [integral_fintype hf]
  unfold DiagTrace
  have hmass (x : BitWord n) :
      (projectiveLimitMeasure (π n ⁻¹' ({x} : Set (BitWord n)))).toReal =
        (1 / 2 : ℝ) ^ n := by
    change (projectiveLimitMeasure
      {q : PrefixProjectiveLimit | π n q = x}).toReal = _
    rw [projectiveLimitMeasure_apply_prefix_fiber]
    norm_num [ENNReal.toReal_ofNat]
  simp_rw [ν, Measure.real_def, Measure.map_apply (continuous_π n).measurable
    (measurableSet_singleton _), hmass]
  norm_num [Finset.mul_sum]

/-- The projective-limit Bernoulli integral is the normalized trace owned by
the UHF diagonal tower, not merely its duplicate finite-stage trace notation. -/
theorem projectiveLimitMeasure_integral_prefix_eq_stageTrace
    (n : ℕ) (f : DiagAlg n) :
    ∫ q, f (π n q) ∂projectiveLimitMeasure =
      InfoGeometry.Canonical.UHFInductiveLimitBoundary.stageTrace n f := by
  rw [projectiveLimitMeasure_integral_prefix_eq_DiagTrace,
    ← stageTrace_eq_DiagTrace]

end InfoGeometry.Canonical.CantorBernoulliDiagTraceBridge
