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
- `InfoGeometry.Projective.OnShellResidueBCFWBridge.local_dlog_residue`
  reuses the Klein `dlog` theorem to read out the local `2*pi*i` residue.
- `InfoGeometry.Projective.OnShellResidueBCFWBridge.residue_bcfw`
  exposes the residue-balance-to-BCFW implication as explicit data.
- `InfoGeometry.Projective.OnShellResidueBCFWBridge.diagram_compression_count`
  proves only the finite bookkeeping inequality for the supplied `220 -> 1`
  comparison.

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

```lean
residue_bcfw
```

Use this when a separate residue owner supplies a three-pole global residue
balance and an implication from that balance to the chosen BCFW boundary.

## Assumptions Required For The Next Lane

1. **Klein line correspondence.**
   Formalize the Grassmannian `Gr(2,4)` / Klein quadric correspondence and the
   incidence relation between spacetime points and twistor lines.

2. **Positive Grassmannian / amplituhedron cells.**
   Add a formal owner for finite cell labels, boundary strata, and the
   combinatorial moves used by the amplituhedron literature.

3. **BCFW comparison.**
   Prove a concrete comparison between the chosen cooperad/Arnold boundary
   relation and the chosen BCFW recursion datum.

4. **Differential-form realization.**
   Prove that the abstract Arnold generators are realized by the concrete
   logarithmic forms `d log Q(x_i - x_j)` on the non-isotropic configuration
   complement.

5. **Plabic/Rohozhkin comparison.**
   Prove a concrete comparison between plabic square moves and the
   Rohozhkin/Delaunay rational flip matrices.  The existing Rohozhkin file owns
   only rational pentagon matrix identities and presented pure-braid descent.

6. **Rank certificate.**
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
