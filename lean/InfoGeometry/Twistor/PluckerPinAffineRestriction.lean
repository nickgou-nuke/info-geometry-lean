/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.Twistor.PluckerPinEndpointStabilizers

/-!
# Restricting the existing native affine action to the Lorentzian slice

The real six-dimensional embedding has four explicit vanishing coordinates
inside `V55`. This characterizes its range, and the existing quotient-level
affine action reads back from the actual transformed native vector. An
infinity-fixing element preserves the affine normalization exactly. If its
native action also preserves the six-dimensional range, its already defined
affine action preserves the corresponding four-coordinate Lorentzian chart.
This is a restriction theorem, not a classification of that subgroup.
-/

noncomputable section

namespace InfoGeometry.Twistor.PluckerPinAffineRestriction

open InfoGeometry.Clifford.Clifford55
open InfoGeometry.Twistor.PluckerCl55InfinityBridge
open InfoGeometry.Canonical.ProjectiveFoundation
open InfoGeometry.Canonical.PACSplit55Cl55CoordinateBridge
open InfoGeometry.Canonical.Cl55WittPinConformalBoundaryBridge
open ProjectiveAffineConformalClosure55

theorem mem_conformalSix_range_iff (v : V55) :
    v ∈ Set.range conformalSixToV55 ↔
      v.1 1 = 0 ∧ v.1 2 = 0 ∧ v.1 3 = 0 ∧ v.2 3 = 0 := by
  constructor
  · rintro ⟨X, rfl⟩
    simp [conformalSixToV55, conformalSixToPAC55, pacSplit55ToV55]
  · rintro ⟨h1, h2, h3, h4⟩
    refine ⟨v55ConformalReadback v, ?_⟩
    ext i <;> fin_cases i <;>
      simp [conformalSixToV55, conformalSixToPAC55, pacSplit55ToV55,
        v55ConformalReadback, h1, h2, h3, h4]

theorem pac44NativeNullVector_mem_conformalSix_iff (x : PACSplit44) :
    pac44NativeNullVector x ∈ Set.range conformalSixToV55 ↔
      x.x1 = 0 ∧ x.x2 = 0 ∧ x.x3 = 0 ∧ x.y3 = 0 := by
  rw [mem_conformalSix_range_iff]
  simp [pac44NativeNullVector, pacSplit55ToV55, conformalEmbed44to55]

/-- The fixed infinity vector determines the affine scale, not only its zero locus. -/
theorem pinInfinityStabilizer_preserves_chartCoordinate
    (g : pinInfinityStabilizer) (v : V55) :
    chartCoordinate55 (pinNativeOrthogonalAction g.1 v) = chartCoordinate55 v := by
  have hg : pinNativeOrthogonalAction g.1 nativeInfinityVector = nativeInfinityVector := g.2
  have h := Q55_isometry_preserves_polar (pinNativeOrthogonalAction g.1)
    v nativeInfinityVector
  rw [hg, nativeInfinityVector_polar, nativeInfinityVector_polar] at h
  linarith

/-- Read the existing projective action through its actual transformed representative. -/
theorem pinInfinityStabilizerAffinePACAction_representative
    (g : pinInfinityStabilizer) (x : PACSplit44) :
    pinInfinityStabilizerAffinePACAction g x =
      affineChartRetractRep (pinNativeOrthogonalAction g.1 (pac44NativeNullVector x)) := by
  change nativeAffineChartRetractRaw
      (pinProjectiveRepresentation.projectivizationMap g.1 (pac44NativeProjectivePoint x)) = _
  unfold pac44NativeProjectivePoint pacProjectivize
  rw [ProjectiveRepresentation.projectivizationMap_mk]
  rfl

theorem pinInfinityStabilizerAffinePACAction_base_readback
    (g : pinInfinityStabilizer) (x : PACSplit44) :
    pinInfinityStabilizerAffinePACAction g x =
      pacSplit55Base44
        (v55ToPacSplit55 (pinNativeOrthogonalAction g.1 (pac44NativeNullVector x))) := by
  have hGauge : chartCoordinate55
      (pinNativeOrthogonalAction g.1 (pac44NativeNullVector x)) = 1 := by
    rw [pinInfinityStabilizer_preserves_chartCoordinate]
    exact conformalEmbed44to55_chartCoordinate x
  rw [pinInfinityStabilizerAffinePACAction_representative]
  unfold affineChartRetractRep
  rw [hGauge]
  apply pacSplit44_ext <;>
    simp [pacSplit55Base44, v55ToPacSplit55]

/-- Six-slice membership is a concrete extra condition on the native group element. -/
theorem pinInfinityStabilizerAffinePACAction_preserves_lorentz_chart
    (g : pinInfinityStabilizer)
    (hSix : ∀ v : V55, v ∈ Set.range conformalSixToV55 →
      pinNativeOrthogonalAction g.1 v ∈ Set.range conformalSixToV55)
    (x : PACSplit44) (hx : x.x1 = 0 ∧ x.x2 = 0 ∧ x.x3 = 0 ∧ x.y3 = 0) :
    (pinInfinityStabilizerAffinePACAction g x).x1 = 0 ∧
      (pinInfinityStabilizerAffinePACAction g x).x2 = 0 ∧
      (pinInfinityStabilizerAffinePACAction g x).x3 = 0 ∧
      (pinInfinityStabilizerAffinePACAction g x).y3 = 0 := by
  have hv := hSix (pac44NativeNullVector x)
    ((pac44NativeNullVector_mem_conformalSix_iff x).mpr hx)
  have hcoordinates := (mem_conformalSix_range_iff _).mp hv
  rw [pinInfinityStabilizerAffinePACAction_base_readback]
  exact hcoordinates

end InfoGeometry.Twistor.PluckerPinAffineRestriction
