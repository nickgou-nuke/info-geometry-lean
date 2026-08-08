import InfoGeometry.Canonical.SingularBoundaryCorrection

/-!
# Singular Transport System

Scalar transport-level interface sitting one level above the primitive boundary
obstruction package.

This module does not assert a direct-sum decomposition of the ambient space.
Instead it packages the sector contributions of logarithmic transport after:

- quotienting the pure projective/Weyl mode
- isolating regularized null directions
- isolating nilpotent spectral residue
- reading the tangential boundary commutator obstruction
- extracting the surviving reduced-volume scalar
-/

namespace InfoGeometry.Canonical

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

/--
Transport-level singular geometry package.

The boundary obstruction remains primitive in `SingularBoundaryCorrection`;
this structure only records how that obstruction enters the scalar transport
law.
-/
structure SingularTransportSystem (E : Type*)
    [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E] where
  ray : RayGaugeData E
  boundary : SingularBoundaryCorrection E
  logDivergence : ℝ
  radialTerm : ℝ
  projectiveTerm : ℝ
  nilpotentTerm : ℝ
  anomalyTerm : ℝ
  gradedTerm : ℝ
  survivorKind : ReducedVolumeKind
  survivorValue : ℝ
  schurReducedVolume : ℝ
  logDivergence_split :
    logDivergence =
      radialTerm + projectiveTerm + nilpotentTerm + anomalyTerm + gradedTerm
  anomalyTerm_eq_boundaryScale :
    anomalyTerm = boundary.boundaryScale
  regular_radial_transport_closes_of_anomalyTerm_eq_zero :
    anomalyTerm = 0 →
      radialTerm = logDivergence - projectiveTerm - nilpotentTerm - gradedTerm
  survivor_interprets_gradedTerm : gradedTerm = survivorValue
  schur_elimination_realizes_survivor : survivorValue = schurReducedVolume

namespace SingularTransportSystem

variable (S : SingularTransportSystem E)

/-- The anomaly scalar is exactly the boundary obstruction scale. -/
theorem anomalyTerm_eq_projector_commutator_norm :
    S.anomalyTerm = S.boundary.boundaryScale :=
  S.anomalyTerm_eq_boundaryScale

/-- The boundary generator is the property projector commutator. -/
theorem boundaryGenerator_eq_projector_commutator :
    S.boundary.boundaryGenerator =
      S.boundary.spectralProjector * S.boundary.leftProjector
        - S.boundary.leftProjector * S.boundary.spectralProjector :=
  S.boundary.boundaryGenerator_eq_projector_commutator

/-- The scalar boundary scale is the norm of the property projector obstruction. -/
theorem boundaryScale_eq_projectorObstruction_norm :
    S.boundary.boundaryScale =
      ‖S.boundary.spectralProjector * S.boundary.leftProjector
          - S.boundary.leftProjector * S.boundary.spectralProjector‖₊ :=
  S.boundary.boundaryScale_eq_projectorObstruction_norm

/-- Vanishing boundary generator is equivalent to projector commutation. -/
theorem boundaryGenerator_eq_zero_iff_projectors_commute :
    S.boundary.boundaryGenerator = 0
      ↔ S.boundary.spectralProjector * S.boundary.leftProjector =
          S.boundary.leftProjector * S.boundary.spectralProjector :=
  S.boundary.boundaryGenerator_eq_zero_iff_projectors_commute

/--
The carried dilation operator detects the boundary obstruction through the
projector commutator decomposition.
-/
theorem dilation_commutator_decomposes_boundaryGenerator :
    S.boundary.spectralProjector * S.boundary.dilationOperator
        - S.boundary.dilationOperator * S.boundary.spectralProjector =
      ((2 : ℝ)⁻¹) •
        (S.boundary.rightBoundaryGenerator - S.boundary.boundaryGenerator) :=
  S.boundary.dilation_commutator_decomposes_boundaryGenerator

/--
Interface property that the boundary generator exponentiates the appropriate
Krein-side infinitesimal transport.
-/
theorem boundaryGenerator_skew_adjoints_to_krein_isometry :
    star S.boundary.boundaryGenerator = -S.boundary.boundaryGenerator :=
  S.boundary.boundaryGenerator_skew_adjoints_to_krein_isometry

/-- The logarithmic transport observable splits into its sector contributions. -/
theorem logarithmicDivergence_split :
    S.logDivergence =
      S.radialTerm + S.projectiveTerm + S.nilpotentTerm + S.anomalyTerm + S.gradedTerm :=
  S.logDivergence_split

/--
If the boundary obstruction vanishes, the transport law closes on the
non-anomalous sector contributions.
-/
theorem logDivergence_split_of_boundaryScale_eq_zero
    (h0 : S.boundary.boundaryScale = 0) :
    S.logDivergence =
      S.radialTerm + S.projectiveTerm + S.nilpotentTerm + S.gradedTerm := by
  rw [S.logarithmicDivergence_split, S.anomalyTerm_eq_projector_commutator_norm, h0]
  simp [add_assoc]

/--
Vanishing boundary obstruction closes the radial transport law against the
remaining non-anomalous sectors.
-/
theorem regular_radial_transport_closes_of_boundaryScale_eq_zero
    (h0 : S.boundary.boundaryScale = 0) :
    S.radialTerm =
      S.logDivergence - S.projectiveTerm - S.nilpotentTerm - S.gradedTerm := by
  apply S.regular_radial_transport_closes_of_anomalyTerm_eq_zero
  rw [S.anomalyTerm_eq_projector_commutator_norm, h0]

/-- The surviving graded transport coefficient is the selected survivor readout. -/
theorem gradedTerm_eq_survivorValue :
    S.gradedTerm = S.survivorValue :=
  S.survivor_interprets_gradedTerm

/-- The Schur elimination readout agrees with the selected reduced volume. -/
theorem survivorValue_eq_schurReducedVolume :
    S.survivorValue = S.schurReducedVolume :=
  S.schur_elimination_realizes_survivor

end SingularTransportSystem

end InfoGeometry.Canonical
