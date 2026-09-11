import InfoGeometry.Canonical.AnomalyGauge
import InfoGeometry.Algebra.FiniteSpinAlgebra
import InfoGeometry.Canonical.CertifiedInverseKernel
import InfoGeometry.Canonical.ConformalUnification
import InfoGeometry.Projective.Bridge
import InfoGeometry.Projective.ConeKL
import InfoGeometry.Projective.Dynamics
import InfoGeometry.Projective.FaithfulKL
import InfoGeometry.Projective.GaugeQuotient
import InfoGeometry.Projective.GaugeReduction
import InfoGeometry.Projective.LogSum
import InfoGeometry.Projective.LogSumIneq
import InfoGeometry.Projective.Normalize
import InfoGeometry.Projective.Null
import InfoGeometry.Projective.Orthant
import InfoGeometry.Projective.PhysicalKinematics
import InfoGeometry.Projective.Projective
import InfoGeometry.Projective.ProjectiveMap
import InfoGeometry.Projective.Rays
import InfoGeometry.Projective.SelfDualCone
import InfoGeometry.MeasureProjective
import Mathlib.Analysis.InnerProductSpace.Adjoint
import Mathlib.Tactic.NoncommRing

/-!
# Singular Boundary Correction

Projector-first package for the singular boundary correction layer.

This module deliberately avoids asserting a direct-sum decomposition of the
ambient carrier. The first abstraction level is instead:

- quotient/ray data for the Weyl-projective mode
- certified Moore-Penrose/Drazin regularization data
- the canonical boundary commutator obstruction
- a minimal transport-closure interface

Downstream modules can add stronger geometric or graded-volume realizations on
top of this interface.
-/

namespace InfoGeometry.Canonical

open InfoGeometry.Canonical.AnomalyGauge

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

/--
Quotient-first Weyl/projective data.

The radial scale mode is treated as quotient data rather than as a linear
projector on the ambient carrier.
-/
structure RayGaugeData (E : Type*) [NormedAddCommGroup E] [InnerProductSpace ℝ E] where
  QuotientState : Type*
  quotientMap : E → QuotientState
  weylAction : ℝ → E → E
  radialPotential : E → ℝ
  quotientPotential : E → ℝ

/-- Surviving reduced-volume kind after singular elimination. -/
inductive ReducedVolumeKind where
  | det
  | pdet
  | pfaffian
  | berezinian
deriving DecidableEq, Repr

/--
Canonical singular-boundary correction package.

The boundary generator is not stored as independent data: it is canonically
derived from the certified inverse kernel as the left-projector anomaly
commutator.
-/
structure SingularBoundaryCorrection (E : Type*)
    [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E] where
  ray : RayGaugeData E
  kernel : CertifiedInverseKernel E
  dilation : E →L[ℝ] E
  dilation_eq_half_sub_mp_projectors :
    dilation = ((2 : ℝ)⁻¹) • (kernel.mpRangeProjector - kernel.metricProjector)
  spectralProjector_star :
    star kernel.spectralProjector = kernel.spectralProjector
  regularRadialTransport : E →L[ℝ] E
  regularRadialTransportCloses :
    kernel.chiralAnomaly = 0 → regularRadialTransport = 0
  closure_of_zero_boundaryGenerator :
    kernel.chiralAnomaly = 0 → regularRadialTransport = 0
  reducedVolumeKind : ReducedVolumeKind
  /-- The reduced volume kind that survives the graded boundary projection. -/
  gradedSurvivor : ReducedVolumeKind
  boundaryGenerator_skew_adjoints_to_krein_isometry :
    star kernel.chiralAnomaly = -kernel.chiralAnomaly

namespace SingularBoundaryCorrection

variable (S : SingularBoundaryCorrection E)

/-- The certified Drazin spectral projector. -/
abbrev spectralProjector : E →L[ℝ] E :=
  S.kernel.spectralProjector

/-- The certified Moore-Penrose left/domain projector. -/
abbrev leftProjector : E →L[ℝ] E :=
  S.kernel.metricProjector

/-- The certified Moore-Penrose right/range projector. -/
abbrev rightProjector : E →L[ℝ] E :=
  S.kernel.mpRangeProjector

/-- Canonical boundary generator: the left-projector anomaly commutator. -/
abbrev boundaryGenerator : E →L[ℝ] E :=
  S.kernel.chiralAnomaly

/-- Two-sided anomaly variant built from the Moore-Penrose range projector. -/
abbrev rightBoundaryGenerator : E →L[ℝ] E :=
  S.kernel.rightChiralAnomaly

/-- Scalar shadow of the boundary obstruction. -/
noncomputable abbrev boundaryScale : ℝ :=
  S.kernel.chiralScale

/-- The dilation operator carried by the package. -/
abbrev dilationOperator : E →L[ℝ] E :=
  S.dilation

/-- The boundary generator is exactly the certified projector commutator. -/
theorem boundaryGenerator_eq_projector_commutator :
    S.boundaryGenerator =
      S.spectralProjector * S.leftProjector - S.leftProjector * S.spectralProjector := by
  rfl

/-- The right boundary generator is the spectral/range-projector commutator. -/
theorem rightBoundaryGenerator_eq_projector_commutator :
    S.rightBoundaryGenerator =
      S.spectralProjector * S.rightProjector - S.rightProjector * S.spectralProjector := by
  rfl

/-- The scalar boundary scale is the norm of the projector obstruction. -/
theorem boundaryScale_eq_projectorObstruction_norm :
    S.boundaryScale =
      ‖S.spectralProjector * S.leftProjector - S.leftProjector * S.spectralProjector‖₊ := by
  simp [boundaryScale, CertifiedInverseKernel.chiralScale,
    CertifiedInverseKernel.toInverseKernel', InverseKernel.chiralScale, InverseKernel.chiralAnomaly]

/-- Vanishing boundary generator is equivalent to projector commutation. -/
theorem boundaryGenerator_eq_zero_iff_projectors_commute :
    S.boundaryGenerator = 0
      ↔ S.spectralProjector * S.leftProjector = S.leftProjector * S.spectralProjector := by
  simp [boundaryGenerator, CertifiedInverseKernel.chiralAnomaly,
    CertifiedInverseKernel.toInverseKernel', InverseKernel.chiralAnomaly, sub_eq_zero]

/-- Projector commutation follows from vanishing boundary generator. -/
theorem projectors_commute_of_boundaryGenerator_eq_zero
    (hZero : S.boundaryGenerator = 0) :
    S.spectralProjector * S.leftProjector = S.leftProjector * S.spectralProjector :=
  (S.boundaryGenerator_eq_zero_iff_projectors_commute).mp hZero

/-- Vanishing projector commutator kills the boundary generator. -/
theorem boundaryGenerator_eq_zero_of_projectors_commute
    (hComm :
      S.spectralProjector * S.leftProjector = S.leftProjector * S.spectralProjector) :
    S.boundaryGenerator = 0 :=
  (S.boundaryGenerator_eq_zero_iff_projectors_commute).mpr hComm

/-- The boundary generator is skew-adjoint once the spectral projector is. -/
theorem boundaryGenerator_skew :
    star S.boundaryGenerator = -S.boundaryGenerator := by
  exact
    commutator_is_skew_adjoint S.spectralProjector S.leftProjector
      S.spectralProjector_star S.kernel.metricProjector_star

/-- The carried dilation operator is exactly the Moore-Penrose half-difference. -/
theorem dilationOperator_eq_half_sub_mp_projectors :
    S.dilationOperator = ((2 : ℝ)⁻¹) • (S.rightProjector - S.leftProjector) :=
  S.dilation_eq_half_sub_mp_projectors

/--
The commutator of the spectral projector with the dilation operator decomposes
as half the difference between the right and left boundary generators.
-/
theorem dilation_commutator_decomposes_boundaryGenerator :
    S.spectralProjector * S.dilationOperator - S.dilationOperator * S.spectralProjector =
      ((2 : ℝ)⁻¹) • (S.rightBoundaryGenerator - S.boundaryGenerator) := by
  apply ContinuousLinearMap.ext
  intro x
  rw [S.dilationOperator_eq_half_sub_mp_projectors]
  unfold rightBoundaryGenerator boundaryGenerator
  unfold CertifiedInverseKernel.rightChiralAnomaly CertifiedInverseKernel.chiralAnomaly
  unfold CertifiedInverseKernel.toInverseKernel'
  unfold InverseKernel.rightChiralAnomaly InverseKernel.chiralAnomaly
  simp [sub_eq_add_neg, smul_add]
  abel_nf

/-- Zero boundary scale is equivalent to vanishing boundary generator. -/
theorem boundaryScale_eq_zero_iff_boundaryGenerator_eq_zero :
    S.boundaryScale = 0 ↔ S.boundaryGenerator = 0 := by
  simp [boundaryScale, boundaryGenerator,
    CertifiedInverseKernel.chiralScale, CertifiedInverseKernel.chiralAnomaly,
    CertifiedInverseKernel.toInverseKernel', InverseKernel.chiralScale, InverseKernel.chiralAnomaly]

/--
If the scalar obstruction vanishes, the package closes to regular radial
transport.
-/
theorem regular_radial_transport_closes_of_boundaryScale_eq_zero
    (hScale : S.boundaryScale = 0) :
    S.regularRadialTransport = 0 := by
  exact S.closure_of_zero_boundaryGenerator
    ((S.boundaryScale_eq_zero_iff_boundaryGenerator_eq_zero).mp hScale)

end SingularBoundaryCorrection

end InfoGeometry.Canonical
