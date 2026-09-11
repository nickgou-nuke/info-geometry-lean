import Mathlib
import InfoGeometry.Algebra.FiniteSpinAlgebra
import InfoGeometry.Canonical.TriColorModularBoundaryFlow

namespace InfoGeometry.Topology

open InfoGeometry.Canonical

/-!
# Continuous common boundary flow for the three local Zorn sectors

The topology on the projective boundary is intentionally supplied by the
caller.  This owner proves inheritance of continuity from the common action;
it does not silently equip the quotient with an artificial discrete topology.
-/

structure ContinuousTriColorModularBoundaryData
    [TopologicalSpace RealProjectiveBoundary] where
  common_continuous : Continuous
    (fun p : ℝ × RealProjectiveBoundary =>
      modularBoostProjectiveAction p.1 p.2)

theorem modularBoostProjectiveAction_zero :
    modularBoostProjectiveAction 0 = id := by
  unfold modularBoostProjectiveAction
  rw [modularBoostSL2_zero]
  exact localSL2ProjectiveAction_one

theorem modularBoostProjectiveAction_add (s t : ℝ) :
    modularBoostProjectiveAction (s + t) =
      modularBoostProjectiveAction s ∘ modularBoostProjectiveAction t := by
  unfold modularBoostProjectiveAction
  rw [modularBoostSL2_add]
  exact localSL2ProjectiveAction_mul _ _

theorem continuous_redBoundaryFlow
    [TopologicalSpace RealProjectiveBoundary]
    (data : ContinuousTriColorModularBoundaryData) :
    Continuous (fun p : ℝ × RealProjectiveBoundary =>
      redBoundaryFlow p.1 p.2) := by
  simpa only [red_modularBoundaryFlow_eq_common] using data.common_continuous

theorem continuous_greenBoundaryFlow
    [TopologicalSpace RealProjectiveBoundary]
    (data : ContinuousTriColorModularBoundaryData) :
    Continuous (fun p : ℝ × RealProjectiveBoundary =>
      greenBoundaryFlow p.1 p.2) := by
  simpa only [green_modularBoundaryFlow_eq_common] using data.common_continuous

theorem continuous_blueBoundaryFlow
    [TopologicalSpace RealProjectiveBoundary]
    (data : ContinuousTriColorModularBoundaryData) :
    Continuous (fun p : ℝ × RealProjectiveBoundary =>
      blueBoundaryFlow p.1 p.2) := by
  simpa only [blue_modularBoundaryFlow_eq_common] using data.common_continuous

theorem redBoundaryFlow_zero (p : RealProjectiveBoundary) :
    redBoundaryFlow 0 p = p := by
  rw [red_modularBoundaryFlow_eq_common]
  rw [modularBoostProjectiveAction_zero]
  rfl

theorem redBoundaryFlow_add (s t : ℝ) (p : RealProjectiveBoundary) :
    redBoundaryFlow (s + t) p =
      redBoundaryFlow s (redBoundaryFlow t p) := by
  rw [red_modularBoundaryFlow_eq_common,
    red_modularBoundaryFlow_eq_common,
    red_modularBoundaryFlow_eq_common,
    modularBoostProjectiveAction_add]
  rfl

theorem greenBoundaryFlow_zero (p : RealProjectiveBoundary) :
    greenBoundaryFlow 0 p = p := by
  rw [green_modularBoundaryFlow_eq_common]
  rw [modularBoostProjectiveAction_zero]
  rfl

theorem greenBoundaryFlow_add (s t : ℝ) (p : RealProjectiveBoundary) :
    greenBoundaryFlow (s + t) p =
      greenBoundaryFlow s (greenBoundaryFlow t p) := by
  rw [green_modularBoundaryFlow_eq_common,
    green_modularBoundaryFlow_eq_common,
    green_modularBoundaryFlow_eq_common,
    modularBoostProjectiveAction_add]
  rfl

theorem blueBoundaryFlow_zero (p : RealProjectiveBoundary) :
    blueBoundaryFlow 0 p = p := by
  rw [blue_modularBoundaryFlow_eq_common]
  rw [modularBoostProjectiveAction_zero]
  rfl

theorem blueBoundaryFlow_add (s t : ℝ) (p : RealProjectiveBoundary) :
    blueBoundaryFlow (s + t) p =
      blueBoundaryFlow s (blueBoundaryFlow t p) := by
  rw [blue_modularBoundaryFlow_eq_common,
    blue_modularBoundaryFlow_eq_common,
    blue_modularBoundaryFlow_eq_common,
    modularBoostProjectiveAction_add]
  rfl

theorem triColor_continuous_common_flow
    [TopologicalSpace RealProjectiveBoundary]
    (data : ContinuousTriColorModularBoundaryData) :
    Continuous (fun p : ℝ × RealProjectiveBoundary =>
      modularBoostProjectiveAction p.1 p.2) :=
  data.common_continuous

end InfoGeometry.Topology
