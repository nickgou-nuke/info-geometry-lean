import InfoGeometry.Canonical.BottDirac
import InfoGeometry.Canonical.ChiralAnomaly
import InfoGeometry.Canonical.CalabiYauMetricRicci
import InfoGeometry.Canonical.CalabiYauRNMongeAmpere
import InfoGeometry.Canonical.KMSSinkhornSeedState
import InfoGeometry.Canonical.KMSSinkhornScalarPotential
import InfoGeometry.Canonical.KMSSinkhornWeightedTransport
import InfoGeometry.Canonical.KaehlerGeometry
import InfoGeometry.Canonical.RicciMongeAmpere
import InfoGeometry.Canonical.SingularTransportSystem
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.LinearAlgebra.Matrix.Kronecker

/-!
# The Grand Unification of the Physics of Information in Lean 4

Capstone synthesis layer connecting thermodynamic Sinkhorn/KMS closure,
geometric Ricci/Calabi-Yau closure, and algebraic Bott-Dirac closure.
-/

open scoped TensorProduct
open scoped Kronecker

namespace InfoGeometry.Canonical.GrandSynthesis

open InfoGeometry.Krein
open InfoGeometry.Canonical.MoE
open InfoGeometry.Canonical.BottDirac
open InfoGeometry.Canonical.CalabiYauBridge
open InfoGeometry.Canonical.ChiralAnomaly
open InfoGeometry.Canonical.KMSSinkhornBridge
open InfoGeometry.Canonical.KaehlerGeometry
open InfoGeometry.Canonical.RicciMongeAmpere
open InfoGeometry.Canonical.SpectralInference

section SingularBoundaryExtension

variable {E : Type*}
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

/--
Singular extension of the bulk transport law:
when the property boundary obstruction vanishes, the logarithmic transport
observable closes on the non-anomalous sector contributions.
-/
private theorem logDivergence_eq_bulkSectors_of_boundaryScale_eq_zero
    (S : SingularTransportSystem E)
    (hBoundary : S.boundary.boundaryScale = 0) :
    S.logDivergence =
      S.radialTerm + S.projectiveTerm + S.nilpotentTerm + S.gradedTerm := by
  exact S.logDivergence_split_of_boundaryScale_eq_zero hBoundary

/--
Singular extension of bulk radial closure:
if the boundary obstruction vanishes, the radial term is determined by the
remaining non-anomalous sectors.
-/
private theorem radial_transport_closes_of_boundaryScale_eq_zero
    (S : SingularTransportSystem E)
    (hBoundary : S.boundary.boundaryScale = 0) :
    S.radialTerm =
      S.logDivergence - S.projectiveTerm - S.nilpotentTerm - S.gradedTerm := by
  exact S.regular_radial_transport_closes_of_boundaryScale_eq_zero hBoundary

/--
The scalar anomaly term is exactly the norm-shadow of the property projector
commutator obstruction carried by the primitive boundary layer.
-/
private theorem anomalyTerm_eq_projectorObstruction_norm
    (S : SingularTransportSystem E) :
    S.anomalyTerm =
      ‖S.boundary.spectralProjector * S.boundary.leftProjector
          - S.boundary.leftProjector * S.boundary.spectralProjector‖₊ := by
  rw [S.anomalyTerm_eq_projector_commutator_norm,
    S.boundary.boundaryScale_eq_projectorObstruction_norm]

/--
Boundary-anomaly freeness is equivalent to commutation of the property Drazin
and Moore-Penrose projectors in the primitive singular boundary layer.
-/
private theorem boundaryGenerator_eq_zero_iff_projectors_commute
    (S : SingularTransportSystem E) :
    S.boundary.boundaryGenerator = 0
      ↔ S.boundary.spectralProjector * S.boundary.leftProjector =
          S.boundary.leftProjector * S.boundary.spectralProjector := by
  exact S.boundaryGenerator_eq_zero_iff_projectors_commute

/--
Vanishing boundary generator forces the primitive singular boundary layer to
close to regular radial transport.
-/
theorem regularRadialTransportCloses_of_boundaryGenerator_eq_zero
    (S : SingularTransportSystem E)
    (hZero : S.boundary.boundaryGenerator = 0) :
    S.boundary.regularRadialTransport = 0 := by
  have hScale : S.boundary.boundaryScale = 0 := by
    exact (S.boundary.boundaryScale_eq_zero_iff_boundaryGenerator_eq_zero).mpr hZero
  exact S.boundary.regular_radial_transport_closes_of_boundaryScale_eq_zero hScale

end SingularBoundaryExtension

end InfoGeometry.Canonical.GrandSynthesis
