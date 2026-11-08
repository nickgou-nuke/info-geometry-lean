import InfoGeometry.Canonical.CalabiYauMetricRicci
import InfoGeometry.Algebra.FiniteSpinAlgebra
import InfoGeometry.Canonical.SingularTransportSystem

/-!
# Calabi-Yau Singular Bridge

Bridge layer sitting above the regular Calabi-Yau zero branch and below the
full singular transport program.

The regular branch is handled in `CalabiYauBridge`: unit relative volume forces
the metric log-determinant to vanish, which collapses the metric-derived Ricci
proxy and yields Ricci-flat / vacuum Einstein closure.

This file records the complementary transport-level statement: once the regular
radial log-det term dies, the remaining logarithmic transport observable is the
singular complement carried by the projective, nilpotent, anomaly, and graded
sectors.
-/

namespace InfoGeometry.Canonical

open InfoGeometry.Canonical.CalabiYauBridge
open InfoGeometry.Canonical.KaehlerGeometry
open InfoGeometry.Canonical.RicciMongeAmpere

section Bridge

variable {E : Type*}
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
  [FiniteDimensional ℝ E]

/--
Bridge from the regular Calabi-Yau zero branch to the singular transport
interface.

The singular transport system is kept abstract, but its radial term is
identified with the metric log-determinant on the Kähler side.
-/
structure CalabiYauSingularTransportBridge (E : Type*)
    [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
    [FiniteDimensional ℝ E] where
  system : SingularTransportSystem E
  geometry : KaehlerInformationGeometry E
  point : E
  radialTerm_eq_metricLogDet :
    system.radialTerm = metricLogDet geometry.H point

namespace CalabiYauSingularTransportBridge

variable (B : CalabiYauSingularTransportBridge E)

/--
On the unit-volume nondegenerate branch, the radial singular-transport term
vanishes because it is identified with the metric log-determinant.
-/
theorem radialTerm_eq_zero_of_unitRelativeVolume
    (hUnit : UnitRelativeVolumeState B.geometry)
    (hdet : MetricOpNondegenerate B.geometry.H) :
    B.system.radialTerm = 0 := by
  rw [B.radialTerm_eq_metricLogDet]
  exact metricLogDet_eq_zero_of_unitRelativeVolume
    (K := B.geometry) hUnit hdet B.point

/--
Once the regular radial branch dies, logarithmic transport reduces to the
singular complement carried by the projective, nilpotent, anomaly, and graded
sectors.
-/
theorem logDivergence_eq_singularComplement_of_unitRelativeVolume
    (hUnit : UnitRelativeVolumeState B.geometry)
    (hdet : MetricOpNondegenerate B.geometry.H) :
    B.system.logDivergence =
      B.system.projectiveTerm + B.system.nilpotentTerm
        + B.system.anomalyTerm + B.system.gradedTerm := by
  rw [B.system.logDivergence_split, B.radialTerm_eq_zero_of_unitRelativeVolume hUnit hdet]
  simp [add_left_comm, add_comm]

/--
If the regular radial branch dies and the boundary obstruction also vanishes,
the remaining logarithmic transport observable closes on the quotient,
nilpotent, and graded sectors alone.
-/
theorem logDivergence_eq_projective_nilpotent_graded_of_unitRelativeVolume_of_boundaryScale_eq_zero
    (hUnit : UnitRelativeVolumeState B.geometry)
    (hdet : MetricOpNondegenerate B.geometry.H)
    (hBoundary : B.system.boundary.boundaryScale = 0) :
    B.system.logDivergence =
      B.system.projectiveTerm + B.system.nilpotentTerm + B.system.gradedTerm := by
  rw [B.system.logDivergence_split_of_boundaryScale_eq_zero hBoundary,
    B.radialTerm_eq_zero_of_unitRelativeVolume hUnit hdet]
  simp [add_left_comm, add_comm]

/--
Metric-derived regular closure plus the transport-level singular complement.
-/
theorem isRicciFlat_and_logDivergence_eq_singularComplement_of_unitRelativeVolume_metricDerived
    (R : RicciTensor E)
    (hUnit : UnitRelativeVolumeState B.geometry)
    (hM : MetricDerivedRNRicciBridge R B.geometry B.point) :
    IsRicciFlat R ∧
      B.system.logDivergence =
        B.system.projectiveTerm + B.system.nilpotentTerm
          + B.system.anomalyTerm + B.system.gradedTerm := by
  have hdet : MetricOpNondegenerate B.geometry.H := hM.2.1
  refine ⟨?_, ?_⟩
  · exact isRicciFlat_of_unitRelativeVolume_metricDerived
      (R := R) (K := B.geometry) (x := B.point) hUnit hM
  · exact B.logDivergence_eq_singularComplement_of_unitRelativeVolume
      hUnit hdet

/--
If the regular radial branch dies and the boundary obstruction also vanishes,
metric-derived unit-volume geometry is simultaneously Ricci-flat and supported
only on the projective, nilpotent, and graded singular sectors.
-/
theorem isRicciFlat_and_logDivergence_eq_projective_nilpotent_graded_of_unitRelativeVolume_metricDerived_of_boundaryScale_eq_zero
    (R : RicciTensor E)
    (hUnit : UnitRelativeVolumeState B.geometry)
    (hM : MetricDerivedRNRicciBridge R B.geometry B.point)
    (hBoundary : B.system.boundary.boundaryScale = 0) :
    IsRicciFlat R ∧
      B.system.logDivergence =
        B.system.projectiveTerm + B.system.nilpotentTerm + B.system.gradedTerm := by
  have hdet : MetricOpNondegenerate B.geometry.H := hM.2.1
  refine ⟨?_, ?_⟩
  · exact isRicciFlat_of_unitRelativeVolume_metricDerived
      (R := R) (K := B.geometry) (x := B.point) hUnit hM
  · exact
      B.logDivergence_eq_projective_nilpotent_graded_of_unitRelativeVolume_of_boundaryScale_eq_zero
        hUnit hdet hBoundary

/--
Metric-derived vacuum Einstein closure plus transport reduction to the pure
singular complement when the radial branch vanishes.
-/
theorem vacuumEinsteinEquation_and_logDivergence_eq_singularComplement_of_unitRelativeVolume_metricDerived
    (R : RicciTensor E)
    (Λ : ℝ)
    (hUnit : UnitRelativeVolumeState B.geometry)
    (hM : MetricDerivedRNRicciBridge R B.geometry B.point) :
    VacuumEinsteinEquationAt R B.geometry B.point (2 * Λ) Λ ∧
      B.system.logDivergence =
        B.system.projectiveTerm + B.system.nilpotentTerm
          + B.system.anomalyTerm + B.system.gradedTerm := by
  have hdet : MetricOpNondegenerate B.geometry.H := hM.2.1
  refine ⟨?_, ?_⟩
  · exact vacuumEinsteinEquation_of_unitRelativeVolume_metricDerived
      (R := R) (K := B.geometry) (x := B.point) (Λ := Λ) hUnit hM
  · exact B.logDivergence_eq_singularComplement_of_unitRelativeVolume
      hUnit hdet

/--
If both the regular radial branch and the boundary anomaly branch vanish, the
metric-derived unit-volume geometry satisfies the vacuum Einstein equation and
the remaining logarithmic transport is supported only on the projective,
nilpotent, and graded sectors.
-/
theorem vacuumEinsteinEquation_and_logDivergence_eq_projective_nilpotent_graded_of_unitRelativeVolume_metricDerived_of_boundaryScale_eq_zero
    (R : RicciTensor E)
    (Λ : ℝ)
    (hUnit : UnitRelativeVolumeState B.geometry)
    (hM : MetricDerivedRNRicciBridge R B.geometry B.point)
    (hBoundary : B.system.boundary.boundaryScale = 0) :
    VacuumEinsteinEquationAt R B.geometry B.point (2 * Λ) Λ ∧
      B.system.logDivergence =
        B.system.projectiveTerm + B.system.nilpotentTerm + B.system.gradedTerm := by
  have hdet : MetricOpNondegenerate B.geometry.H := hM.2.1
  refine ⟨?_, ?_⟩
  · exact vacuumEinsteinEquation_of_unitRelativeVolume_metricDerived
      (R := R) (K := B.geometry) (x := B.point) (Λ := Λ) hUnit hM
  · exact
      B.logDivergence_eq_projective_nilpotent_graded_of_unitRelativeVolume_of_boundaryScale_eq_zero
        hUnit hdet hBoundary

end CalabiYauSingularTransportBridge

end Bridge

end InfoGeometry.Canonical
