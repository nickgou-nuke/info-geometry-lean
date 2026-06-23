# Twistor / Amplituhedron Synthesis Ledger

Status: conservative bridge ledger, not theorem authority.

Lean authority lives in:

- `lean/InfoGeometry/Projective/TwistorAmplituhedronConfigurationBridge.lean`
- `lean/InfoGeometry/Projective/KleinQuadric.lean`
- `lean/InfoGeometry/Projective/KleinQuadricIncidence.lean`
- `lean/InfoGeometry/Projective/NonIsoConf3RankIngestion.lean`
- `lean/InfoGeometry/Projective/RohozhkinDelaunayScramblingBridge.lean`
- `lean/InfoGeometry/Projective/QDeformedTwistorAmplituhedronBridge.lean`
- `lean/InfoGeometry/Projective/OnShellResidueBCFWBridge.lean`
- `lean/InfoGeometry/Projective/PenroseDelaunayKleinAmplituhedronBridge.lean`
- `lean/InfoGeometry/Projective/PenroseDAGAmplituhedronRosetta.lean`
- `lean/InfoGeometry/Topology/AmplituhedronBoundary.lean`
- `lean/InfoGeometry/Topology/AmplituhedronBoundaryExternalRankBridge.lean`
- `lean/InfoGeometry/Topology/AmplituhedronBoundaryRank32.lean`
- `lean/InfoGeometry/Projective/KuzminCuntzPath.lean`
- `lean/InfoGeometry/Projective/Twistor/Basic.lean`

## Arango / LeanTrail Owner Map

This lane must be discovered through the live LeanTrail syntax graph before
new sockets are added.  On the current graph, the relevant owner slice was
refreshed with:

```bash
lake env lean --run tools/leantrail/DumpLeanGraph.lean \
  lean/InfoGeometry/Topology/AmplituhedronBoundary.lean \
  lean/InfoGeometry/Topology/AmplituhedronBoundaryRank32.lean \
  lean/InfoGeometry/Topology/AmplituhedronBoundaryExternalRankBridge.lean \
  lean/InfoGeometry/Projective/ArnoldRelations.lean \
  lean/InfoGeometry/Projective/TwistorAmplituhedronBridge.lean \
  lean/InfoGeometry/Projective/TwistorAmplituhedronBoundary.lean \
  lean/InfoGeometry/Projective/TwistorAmplituhedronConfigurationBridge.lean \
  lean/InfoGeometry/Projective/BostConnesAmplituhedronSynthesis.lean \
  lean/InfoGeometry/Projective/QDeformedTwistorAmplituhedronBridge.lean \
  lean/InfoGeometry/Projective/PenroseDAGAmplituhedronRosetta.lean \
  lean/InfoGeometry/Projective/PenroseDelaunayKleinAmplituhedronBridge.lean \
  lean/InfoGeometry/Projective/RohozhkinDelaunayBraiding.lean \
  lean/InfoGeometry/Projective/RohozhkinDelaunayScramblingBridge.lean \
  lean/InfoGeometry/Topology/RohozhkinDelaunayBraiding.lean \
  lean/InfoGeometry/Topology/DelaunayPureBraidRepresentation.lean \
  lean/InfoGeometry/Topology/DelaunayPureBraidInvariant.lean \
  > /tmp/amplituhedron_owner_syntax.jsonl

python3 tools/leantrail/check_dump_shape.py --expect-keyword theorem \
  < /tmp/amplituhedron_owner_syntax.jsonl

python3 tools/leantrail/ingest_syntax_to_arango.py \
  /tmp/amplituhedron_owner_syntax.jsonl --execute-http
```

After refresh, the syntax graph contains the following owner declarations.
These are navigation evidence only; the Lean files remain proof authority.

- `InfoGeometry.Projective.ArnoldRelations` owns
  `ArnoldExterior`, `arnoldMixedRelation`, and
  `arnold_mixed_relation_vanishes_under_kernel_membership`.
- `InfoGeometry.Projective.Amplituhedron`, in
  `Projective/ArnoldRelations.lean`, owns the quotient-level
  `ArnoldRel`, `ArnoldAlgebra`, `omega`, `omega_symm`, and
  `arnold_mixed_relation_quotient_zero`.
- `InfoGeometry.Projective.TwistorAmplituhedronConfigurationBridge` owns the
  three-line Klein packet, the supplied `ArnoldBCFWInterface`, the
  `RohozhkinPlabicInterface`, rank-budget readbacks, and the conservative
  q-deformation interface.
- `InfoGeometry.Projective.TwistorAmplituhedronBoundary` owns the concrete
  twistor-incidence-to-null-separation readback and the explicit boundary
  comparison socket.
- `InfoGeometry.Projective.PenroseDAGAmplituhedronRosetta` owns the common
  carrier formulation for DAG graph, split-quaternion, Penrose-net,
  Klein-quadric, amplituhedron, and Delaunay-tessellation lanes.
- `InfoGeometry.Projective.PenroseDelaunayKleinAmplituhedronBridge` owns the
  commuting-route corridor from DAG/Penrose/Klein/Delaunay carriers into a
  supplied amplituhedron carrier.
- `InfoGeometry.Topology.AmplituhedronBoundary` owns the finite algebraic
  three-edge boundary packet, the Arnold-boundary comparison, and the
  nilpotence-driven channel factorizations.
- `InfoGeometry.Topology.AmplituhedronBoundaryRank32` owns the concrete
  `Fin 32` carrier, the `16 + 16` split, and the Arnold exterior-product
  labelled readout.
- `InfoGeometry.Topology.AmplituhedronBoundaryExternalRankBridge` owns the
  external local-rank `8` times spin-tiling multiplicity `4` arithmetic bridge
  to the finite boundary carrier cardinality.
- `InfoGeometry.Topology.RohozhkinDelaunayBraiding` and
  `InfoGeometry.Topology.DelaunayPureBraidRepresentation` own the finite
  Rohozhkin/Delaunay pentagon and pure-braid representation descent surfaces.

## Closed Kernel Surface

- Three-line Plucker/Klein configurations can be represented with explicit
  pairwise non-incidence hypotheses.
- Klein incidence is the explicit bilinear Plucker pairing from the owner file.
- Penrose projective null twistor space is inhabited by the existing twistor
  owner.
- A supplied external Betti datum with ambient dimension `8`, internal
  consistency, and local rank `8` gives the spin-tiled rank `32`.
- A completed Rohozhkin/Delaunay generator assignment satisfying all pure-braid
  relators descends to the presented pure-braid matrix representation.
- The q-deformation bridge records the Kuzmin open window as `|q| < 1`.
  It proves `q = 0` is inside that window and `q = -1`, `q = 1` are boundary
  endpoint readouts, not interior classification points.
- The finite q-Gram positivity and q-CCR endpoint readbacks are re-exported
  from the existing q-CCR owner files.
- The local `dlog` pole model reuses the existing Klein theorem
  `circleIntegral_grothendieck_dlog`, giving the checked `2*pi*i` residue.
- Any target model whose kernel contains the abstract Arnold mixed relation
  kills that relation.
- The illustrative `220 -> 1` diagram/carrier comparison is finite
  arithmetic only.
- The Penrose/DAG/amplituhedron Rosetta lane is formalized as explicit
  common-carrier data.  Transport between DAG graph, split-quaternion,
  Penrose-net, Klein-quadric, amplituhedron, and Delaunay-tessellation lanes is
  by supplied equivalences, not by a proved geometric identity.
- The algebraic three-edge boundary packet proves nilpotence-driven left
  factorization for the formal expression
  `e12*omega23 + e23*omega31 + e31*omega12`.
- The rank-32 boundary carrier is a concrete `Fin 32` split into a chiral half
  of `16` indices and an anti-chiral half of `16` indices.
- External rank data with ambient dimension `8`, internal list consistency, and
  local rank `8` has spin-tiled rank equal to the cardinality of the finite
  rank-32 boundary carrier.

## Explicit Interfaces

- Amplituhedron boundary comparison is a supplied implication from Klein
  incidence to a selected boundary predicate.
- Arnold/cooperad to BCFW comparison is a supplied implication.
- Rohozhkin-to-plabic comparison is supplied data.
- Rank `32` is matched to a supplied `stateBudget = 32`; no physical multiplet
  identification is proved.
- q-stability of a selected twistor/amplituhedron carrier is supplied as an
  explicit carrier equivalence plus preservation predicates.
- The route from three-pole residue balance to BCFW recursion is a supplied
  implication.
- The route from Arnold-kernel vanishing to concrete residue balance is a
  supplied implication.
- The route identifying the DAG graph, split-quaternion matrix model, Penrose
  net, Klein quadric, amplituhedron boundary, and Delaunay tessellation is a
  supplied commuting carrier diagram.
- The route from the algebraic boundary packet to a concrete amplituhedron
  volume form, BCFW recursion, or a de Rham cohomology class is not supplied in
  `Topology.AmplituhedronBoundary`.
- The route from the finite rank-32 carrier to a concrete cohomology basis or
  physical supermultiplet is not supplied in
  `Topology.AmplituhedronBoundaryRank32`.
- The route from external rank arithmetic to an independently certified
  D-module/de Rham computation is not supplied in
  `Topology.AmplituhedronBoundaryExternalRankBridge`.

## Non-Claims

- No theorem identifies `Conf_3` de Rham cohomology with an amplituhedron
  volume.
- No theorem identifies Arnold relations with BCFW recursion.
- No theorem identifies Rohozhkin Delaunay flips with plabic square moves.
- No theorem identifies the configured rank `32` with an `N=4` SYM
  supermultiplet.
- No theorem identifies the finite `Fin 32` boundary carrier with a
  32-dimensional de Rham cohomology group.
- No theorem proves Kuzmin's C*-classification route inside Lean.  The repo
  only owns finite q-CCR algebra and explicit comparison sockets.
- Not established: q-CCR/Cuntz-Toeplitz stability implying amplituhedron
  invariance, q-deformed BCFW recursion, or scattering-amplitude stability.
- No theorem proves a Feynman-diagram reduction, a residue theorem on a
  compactified configuration space, or a Parke-Taylor/amplitude formula.
- No theorem proves a scattering-amplitude, unitarity, or physical-spacetime
  result from this bridge.
- No theorem proves that the DAG graph, Penrose net, Delaunay tessellation,
  Klein quadric, split-quaternion model, and amplituhedron are definitionally
  equal, or connected by a proved geometric comparison, without explicit
  comparison maps.

## Companion Witness

`formalizations/twistor_amplituhedron_interface_witness.py` checks only:

- three concrete Plucker lines lie on the Klein quadric;
- their pairwise Klein incidence pairings are nonzero;
- the finite arithmetic budget `8 * 4 = 32`.

`formalizations/qdeformed_twistor_amplituhedron_witness.py` checks only:

- `q = 0` lies inside `abs(q) < 1`;
- `q = -1` and `q = 1` are boundary endpoints;
- the sample finite q-Gram matrix at `q = 1/2` has positive eigenvalues;
- the algebraic q-CCR relation reduces to Toeplitz/CAR/CCR endpoint readouts.

`formalizations/on_shell_residue_bcfw_witness.py` checks only:

- the local model `∮ dz/z = 2*pi*i`;
- a symbolic three-pole balance `r12 + r23 + r31 = 0`;
- the finite bookkeeping arithmetic `220 - 1 = 219`.

`formalizations/penrose_dag_rosetta_witness.py` checks only:

- the six Rosetta lanes are present;
- each lane is assigned to the same finite common-carrier tag;
- all ordered pairwise lane transports are therefore available as bookkeeping
  equalities.

`formalizations/amplituhedron_boundary_witness.py` checks only:

- three formal edge symbols are nilpotent;
- left multiplication by each nilpotent edge kills its own channel;
- the three finite factorization identities match the Lean boundary packet.

`formalizations/amplituhedron_rank32_boundary_witness.py` checks only:

- the finite carrier has `32` indices;
- indices `0..15` and `16..31` form two disjoint halves;
- each half has cardinality `16`, and together they exhaust the carrier.

`formalizations/amplituhedron_external_rank_bridge_witness.py` checks only:

- the candidate local Betti vector has sum `8`;
- multiplying by the spin-tiling multiplicity `4` gives `32`;
- this arithmetic total matches the finite boundary carrier cardinality.
