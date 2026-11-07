# Twistor / Amplituhedron `Conf3` Roadmap

**Status:** conservative formalization roadmap and theorem-surface ledger.

This note records the safe bridge between the existing non-isotropic
configuration-space work, twistor incidence, Klein quadric files, and
Rohozhkin/Delaunay pentagon files.  It is not a proof that `Conf3` is an
amplituhedron and not a proof that the current rank fixture computes an
`N = 4` SYM superamplitude state space.

## Stable Lemmas

- `InfoGeometry.Twistor.Incidence.incident_points_null_separated`
  proves that two spacetime points incident with the same twistor with nonzero
  primary spinor are null-separated.
- `InfoGeometry.Projective.Twistor.penroseProjectiveNullTwistor_nonempty`
  gives an inhabited projective null twistor space.
- `InfoGeometry.Projective.NonIsoConf3RankIngestion.candidateLocalBettiData_spinTiled_rank32`
  proves the current finite candidate rank arithmetic after the spin-tiling
  multiplicity.  It is a candidate fixture, not an external D-module
  certificate.
- `InfoGeometry.Projective.RohozhkinDelaunayBraiding.appendix_pentagon_matrix_identity_readout`
  reads out the Appendix A Rohozhkin rational pentagon block as the identity.
- `InfoGeometry.Projective.ArnoldRelations.arnold_mixed_relation_vanishes_under_kernel_membership`
  proves that any target ring model whose kernel contains the abstract
  three-point Arnold mixed relation kills that relation.
- `InfoGeometry.Projective.TwistorAmplituhedronBridge.common_twistor_incidence_forces_null_boundary`
  exposes the twistor incidence null-boundary theorem at the projective bridge
  layer.
- `InfoGeometry.Projective.TwistorAmplituhedronBridge.rohozhkin_pentagon_face_identity_readout`
  exposes the Rohozhkin pentagon face identity at the same bridge layer.
- `InfoGeometry.Projective.TwistorAmplituhedronBridge.arnold_mixed_relation_kernel_readout`
  exposes the finite Arnold kernel-annihilation readout at the same bridge
  layer.
- `InfoGeometry.Projective.KleinQuadricGrothendieckDeRham.circleIntegral_grothendieck_dlog`
  is the owner of the local `2*pi*i` circle-integral identity; there is no
  separate forwarding residue theorem.
- `InfoGeometry.Topology.GrandUnificationLinker.dag_edge_commutes_with_symmetric_mixed`
  proves commutation of the specified DAG edge with its symmetric mixed
  element. This ring identity is not a residue balance or BCFW theorem.
- `PlabicBoundaryMeasurement.mutatePlucker_eq_minor2_of_plucker_relation`
  identifies the rational `2 × 4` Plücker exchange with the missing minor when
  the denominator minor is nonzero.
- `PlabicBoundaryMeasurement.boundaryMeasurement_cluster_face_weight_readout`
  connects the explicit positive `Gr(2,4)` chart to the abstract Ptolemy
  face-weight identity, including positivity of the exchanged minor. This is a
  matrix-chart/cluster-coordinate bridge, not a graph boundary measurement.
- `PlabicBoundaryMeasurement.boundaryMeasurement_plucker_13_eq_two_route_readout`
  identifies the chart's `Δ₁₃` coordinate with the endpoint entry of an
  explicit three-vertex DAG path-sum matrix. The same owner proves the finite
  path-sum expansion and both resolvent inverse identities. This is a
  chart-to-DAG identity, not a planar plabic graph construction.
- `PlabicBoundaryMeasurement.boundaryMeasurement_plucker_13_eq_diamond_readout`
  gives a four-vertex diamond DAG with two distinct two-edge source-to-sink
  paths of weights `t₁t₃` and `t₂t₄`; its finite Green matrix entry is the same
  `Δ₁₃` coordinate. This removes the compressed direct-edge model as the only
  route witness, while still leaving a planar embedding and boundary trip data
  open.
- `InfoGeometry.Canonical.PlabicBoundaryPostnikovBridge.boundary_measurement_postnikov_channels_and_dag_readout`
  transports the existing Postnikov `Gr(2,4)` boundary-channel split to the
  boundary-measurement chart and identifies its two summands with the direct
  and two-edge DAG route weights. It is a bridge between existing matrix
  owners; it does not prove the graph boundary-measurement map.
- `InfoGeometry.Canonical.PlabicBoundaryPostnikovBridge.boundary_chart_plucker_coordinates_match_zorn_ray`
  maps the two rows of the positive `2 × 4` chart to the existing `Twistor4`
  carrier and proves the exact six-coordinate correspondence between chart
  minors and the Zorn owner's electric/magnetic Plücker split.
- `InfoGeometry.Canonical.PlabicBoundaryPostnikovBridge.boundary_chart_zorn_ray_is_klein_null`
  transports the chart row pair into the existing Klein-quadric theorem and
  proves its Zorn ray is square-zero. This closes the chart-to-single-ray
  carrier/coordinate gap; it does not identify a cluster mutation or second
  scattering ray with a two-ray foam bracket.
- `InfoGeometry.Canonical.PlabicBoundaryPostnikovBridge.positive_boundary_chart_ray_surprise_without_self_foam`
  proves that in the strictly positive chart both Plücker components are
  nonzero while the corresponding simple-ray Zorn square vanishes.
- `InfoGeometry.Canonical.PlabicBoundaryPostnikovBridge.boundary_chart_minor_as_two_ray_scattering_foam`
  uses the complementary coordinate twistor ray to identify `Δ₀₁` with a
  four-twistor bracket and the scalar of its two-ray Zorn square.
- `InfoGeometry.Canonical.PlabicBoundaryPostnikovBridge.positive_boundary_chart_reference_bracket_survives`
  proves this reference-ray bracket is nonzero when the chart coordinate
  `t₂` is positive.
- `InfoGeometry.Canonical.PlabicBoundaryPostnikovBridge.boundary_chart_all_minors_as_reference_brackets`
  identifies all six ordered chart minors with four-twistor brackets against
  complementary coordinate rays.
- `InfoGeometry.Canonical.PlabicBoundaryPostnikovBridge.boundary_chart_all_minors_as_two_ray_scattering_foam`
  proves that each of those six minors is the scalar of a corresponding
  two-ray Zorn scattering square. These reference rays are algebraic
  coordinate rays; this theorem does not assert they arise from a plabic graph
  move. The remaining gap is to connect a genuine square move / mutated chart
  to a compatible second ray and its resulting bracket.
- `InfoGeometry.Archetypes.TwistorAmplituhedronZornBaryon.plucker_ray_and_scattering_projector_defects`
  proves the single-ray projector defect is zero and the paired-ray defect is
  the scalar four-twistor bracket in the concrete Zorn carrier.
- `InfoGeometry.Archetypes.TwistorAmplituhedronZornBaryon.two_ray_projector_defect_ne_zero_iff_bracket_ne_zero`
  identifies the exact nondegeneracy condition for that paired-ray defect.
- `InfoGeometry.Archetypes.TwistorAmplituhedronZornBaryon.plucker_ray_component_nonvanishing_counterexamples`
  refutes the universal claim that both Plücker components of every simple
  ray are nonzero; each component can vanish on a simple ray.
- `InfoGeometry.Archetypes.TwistorAmplituhedronZornBaryon.standard_basis_two_ray_scattering_survives`
  supplies an explicit integer example with four-bracket `1` and nonzero
  two-ray scattering square.
- `InfoGeometry.Canonical.Gr24PositiveTopCell.topCellCoordinateEquiv` and
  `chartMatrix_plucker_readout` identify the gauge-fixed positive top cell with
  its four positive coordinates and record all six Plücker coordinates.
The former `220 -> 1` diagram-count packet was fixed-value bookkeeping, not a
derived amplitudes result, and is not part of the Lean API. Arnold kernel
annihilation remains owned by `InfoGeometry.Projective.ArnoldRelations`.

## Conditional Interfaces

The amplituhedron lane should enter only through explicit comparison data.

```lean
amplituhedron_boundary_readout_of_comparison
```

Use this when a separate owner supplies a map from a null-boundary event to an
amplituhedron boundary datum.

```lean
bcfw_readout_of_cooperad_comparison
```

Use this when a separate owner supplies a comparison from a specific
cooperad/Arnold relation to a BCFW-style readout.

Neither theorem proves the comparison.  They only keep downstream code honest
about the required premise.

The current finite DAG-edge commutation theorem has no residue-balance input.
A genuine residue-to-BCFW result remains an open comparison obligation and
must not be inferred from that algebraic commutation identity.

## Assumptions Required For The Next Lane

1. **Klein line correspondence.**
   Formalize the Grassmannian `Gr(2,4)` / Klein quadric correspondence and the
   incidence relation between spacetime points and twistor lines.

2. **Plabic graph boundary measurement.**
   Construct a finite planar network, define its boundary-measurement map, and
   prove that the local graph square move induces the Plücker exchange above.
   The current matrix family and abstract cluster face weights do not provide
   this graph-level comparison.

   The existing two-ray Zorn identity has survival criterion
   `twistorBracket4 ≠ 0`, not merely nonzero Plücker components. The new typed
   bridge identifies each positive chart point with a simple Zorn ray, but no
   map yet identifies a chart mutation and a paired chart point with the two
   rays whose bracket controls foam survival.

   The finite DAG readout connects one chart minor to a terminating path sum,
   and the Postnikov bridge transports the existing two-channel matrix
   decomposition into that chart. The DAG still lacks a planar embedding,
   boundary sources/sinks and trips, and a local square-move operation.

3. **Positive Grassmannian / amplituhedron cells.**
   Add a formal owner for finite cell labels, boundary strata, and the
   combinatorial moves used by the amplituhedron literature.

4. **BCFW comparison.**
   Prove a concrete comparison between the chosen cooperad/Arnold boundary
   relation and the chosen BCFW recursion datum.

5. **Differential-form realization.**
   Prove that the abstract Arnold generators are realized by the concrete
   logarithmic forms `d log Q(x_i - x_j)` on the non-isotropic configuration
   complement.

6. **Plabic/Rohozhkin comparison.**
   Prove a concrete comparison between plabic square moves and the
   Rohozhkin/Delaunay rational flip matrices.  The existing Rohozhkin file owns
   only rational pentagon matrix identities and presented pure-braid descent.

7. **Rank certificate.**
   Replace the candidate `Conf3` rank fixture with a separately auditable
   external D-module/Singular/Macaulay2 certificate before using it as a final
   cohomology theorem.

## Explicit Non-Claims

- No theorem currently proves `Conf3` is an amplituhedron.
- No theorem currently proves BCFW recursion from Arnold/cooperad relations.
- No theorem currently proves BCFW recursion from residue calculus.
- No theorem currently proves that Rohozhkin/Delaunay flips are plabic graph
  square moves.
- No theorem currently proves a Feynman-diagram compression theorem; the
  `220 -> 1` comparison is bookkeeping arithmetic only.
- No theorem currently identifies the rank arithmetic with an `N = 4` SYM
  supermultiplet.
- No theorem currently derives physical unitarity or scattering amplitudes from
  the de Rham calculation.

## Verification

```bash
lake env lean lean/InfoGeometry/Projective/TwistorAmplituhedronBridge.lean
lake build InfoGeometry.Projective.TwistorAmplituhedronBridge
python3 tools/infra/run_locked_lake_build.py --wait-for-build-lock InfoGeometry.Projective.All
rg -n "sorry|admit|axiom|_valid|_certificate|law_holds" \
  lean/InfoGeometry/Projective/TwistorAmplituhedronBridge.lean
```
