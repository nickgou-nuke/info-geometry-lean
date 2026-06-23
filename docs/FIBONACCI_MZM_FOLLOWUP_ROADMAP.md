# Fibonacci/MZM Follow-Up Roadmap

Status: companion roadmap for the amplituhedron-boundary corridor.

This note records what is already kernel-owned, what can be used as a bridge
assumption, and what remains proof debt. It is not a physics theorem and does
not promote graph/RAG evidence to proof authority.

## Inductive-Colimit Obligation

The finite Fibonacci/MZM surfaces listed below are only the starting stage for
any `n`-indexed theorem family.  A family is not finished until one of the
existing direct-limit or inductive-colimit owners transports it to the
appropriate limit surface, or until the file explicitly states that it is
intentionally finite-stage only.

Current colimit owners already present in the repo include:

- `lean/InfoGeometry/Categorical/FibonacciBraidDirectLimit.lean`
- `lean/InfoGeometry/Categorical/FibonacciGrothendieckLimit.lean`
- `lean/InfoGeometry/Categorical/FibonacciGrothendieckLimitBridge.lean`
- `lean/InfoGeometry/Categorical/FibonacciBraidedTowerCone.lean`
- `lean/InfoGeometry/Canonical/TensorTowerColimit.lean`
- `lean/InfoGeometry/Canonical/InductiveInvarianceTKKPacket.lean`

The follow-up bridge should prefer one of these lanes rather than creating a
new colimit theory unless the new owner is genuinely needed.

The q-CCR corridor now has an explicit conservative limit socket at
`lean/InfoGeometry/Projective/KuzminInductiveLimitBridge.lean`.  It transports
the finite `q = 0`, `q = -1`, and `q = 1` readouts into an abstract limit
carrier, but it does not claim an analytic `KO_∞` identification.  That bridge
is a consumer of the generic colimit discipline above, not a replacement for
it.

## Stable Lean Surface

### Finite Fibonacci Matrix And Braid Readouts

Owner files:

- `lean/InfoGeometry/Categorical/FibonacciBraiding.lean`
- `lean/InfoGeometry/Canonical/FiniteFibonacciPaperBridge.lean`

Stable theorem surface:

- `InfoGeometry.Categorical.FibonacciBraiding.F_sq`
- `InfoGeometry.Categorical.FibonacciBraiding.det_F`
- `InfoGeometry.Categorical.FibonacciBraiding.B_eq_FRF`
- `InfoGeometry.Categorical.FibonacciBraiding.finite_hexagon_shadow`
- `InfoGeometry.Canonical.FiniteFibonacciPaperBridge.fibonacci_fusion_rule`
- `InfoGeometry.Canonical.FiniteFibonacciPaperBridge.fibonacci_vacuum_channel_dimension`
- `InfoGeometry.Canonical.FiniteFibonacciPaperBridge.fibonacci_register_card`
- `InfoGeometry.Canonical.FiniteFibonacciPaperBridge.fibonacci_computational_vector_card`
- `InfoGeometry.Canonical.FiniteFibonacciPaperBridge.fibonacci_monodromy_braid_rewrite`
- `InfoGeometry.Canonical.FiniteFibonacciPaperBridge.fibonacci_monodromy_commute_rewrite`
- `InfoGeometry.Canonical.FiniteFibonacciPaperBridge.fibonacci_compassTransport_braid_rewrite`
- `InfoGeometry.Canonical.FiniteFibonacciPaperBridge.fibonacci_compassTransport_commute_rewrite`

What this gives:

- finite Fibonacci fusion/counting readouts;
- finite matrix facts for the explicit `F`, `R`, and `B = F R F` matrices;
- supplied Artin/Yang-Baxter matrix identity packaging;
- repo-native finite braid-word rewrite invariance.

What it does not give:

- a full `BraidedCategory` instance;
- a conformal-block construction;
- density/universality of braid gates;
- analytic continuation or an infinite anyon limit.

Finite-stage readouts must not be promoted to the terminal surface without an
explicit colimit transport theorem.

### Majorana/Doubled-Core Surface

Owner files:

- `lean/InfoGeometry/Core/MajoranaLiftPacket.lean`
- `lean/InfoGeometry/Physics/BoundaryMajoranaMassGap.lean`

Stable theorem surface:

- `InfoGeometry.Core.MajoranaLiftPacket.K_sq_eq_neg_id`
- `InfoGeometry.Core.canonicalMajoranaLiftPacket_root_laws`
- `InfoGeometry.Physics.BoundaryMajoranaMassGap.majoranaPairGap_eq_zero_iff`
- `InfoGeometry.Physics.BoundaryMajoranaMassGap.pfaffianGap_eq_zero_iff`
- `InfoGeometry.Physics.BoundaryMajoranaMassGap.netChiral_eq_sixteen_of_cMinus_eq_eight`
- `InfoGeometry.Physics.BoundaryMajoranaMassGap.right_minus_left_eq_sixteen_of_cMinus_eq_eight`

What this gives:

- doubled-core involution data with `(Jε)^2 = -Id`;
- scalar Majorana/Pfaffian gap readouts;
- finite chiral central-charge bookkeeping.

What it does not give:

- a theorem identifying boundary defects with physical Majorana zero modes;
- a BdG spectral theorem for the full horizon operator;
- a bulk/boundary index theorem.

### Cuntz/SUSY/Braid Surface

Owner file:

- `lean/InfoGeometry/Canonical/CuntzSuperBraidMoEBridge.lean`

Stable theorem surface:

- `particle_sector_artin`
- `hole_sector_artin`
- `particle_hole_sector_commute`
- `central_generator_particle_to_hole`
- `central_generator_hole_to_particle`
- `cross_sector_parity_odd`
- `isotropic_pair_cross_parity_odd`
- `cuntz6_quotient_hodgeDirac_majorana_sum`
- `finite_cuntz_super_braid_moe_packet`

What this gives:

- finite particle/hole braid rewrite packets;
- parity readouts for the Nambu-sector split;
- a finite Cuntz-super-braid packet.

What it does not give:

- a theorem identifying this packet with Fibonacci MZM braiding;
- a theorem deriving the Cuntz packet from an analytic superconformal field
  theory.

### Amplituhedron/Arnold Boundary Carrier

Owner files:

- `lean/InfoGeometry/Topology/AmplituhedronBoundary.lean`
- `lean/InfoGeometry/Topology/AmplituhedronBoundaryRank32.lean`
- `lean/InfoGeometry/Projective/ArnoldRelations.lean`

Stable theorem surface:

- `superAmplitudeVolume_eq`
- `left_on_shell_factorization_packet`
- `ArnoldBoundaryRealization.superAmplitudeVolume_zero_of_arnold`
- `boundaryRank32State_card`
- `chiralState_card`
- `antiChiralState_card`
- `ArnoldProductRank32Realization.label_card`
- `ArnoldProductRank32Realization.basis_entry_readout`
- `ArnoldProductRank32Realization.basisMatrix_entry`

What this gives:

- theorem-safe three-channel boundary algebra;
- nilpotence-driven factorization readouts;
- a finite `32 = 16 + 16` carrier;
- a labelled Arnold exterior-product readout for the 32 states.

What it does not give:

- a de Rham cohomology computation for `F_Q(C^4,3)`;
- linear independence or spanning of the 32 Arnold product labels;
- a theorem identifying the carrier with an `N = 4` supermultiplet;
- a theorem deriving BCFW recursion from residues.

## Conservative Next Bridge

The next Lean owner should be an interface theorem, not a physics theorem.
Recommended target:

```text
lean/InfoGeometry/Canonical/FibonacciMZMArnoldBridge.lean
```

Recommended structure:

```text
FibonacciMZMArnoldReadout
  finiteFibonacciPacket     -- finite matrix/braid facts from Fibonacci owners
  majoranaPacket            -- doubled-core Majorana root laws
  rank32ArnoldPacket        -- ArnoldProductRank32Realization
  comparisonAssumption      -- explicit Prop supplied by a future owner
```

Recommended theorem shape:

```text
comparisonAssumption -> selected readout
```

This keeps the theorem honest: the comparison from Fibonacci/MZM braiding to the
Arnold rank-32 boundary carrier remains visible as an assumption until a real
owner proves it.

If the comparison depends on a stage index `n`, the theorem should be carried
through the inductive colimit owner rather than left as a frozen finite-stage
fact.

For the next two stage-to-limit lanes in this family, prefer the existing
generic owners rather than inventing parallel machinery:

- configuration-space stabilization should plug into
  `lean/InfoGeometry/Canonical/InductiveColimitBridge.lean`;
- Delaunay/Penrose Bratteli transport should plug into
  `lean/InfoGeometry/Topology/GrandUnificationColimitTransport.lean`.

## Open Debt List

1. Prove or explicitly certificate the rank-32 de Rham cohomology statement for
   the quadric complement.
2. Prove linear independence/spanning for the Arnold exterior-product labels, or
   rename them permanently as a readout carrier rather than a basis.
3. Build the actual categorical layer for Fibonacci anyons if needed:
   objects, tensor product, associator, braiding natural isomorphisms,
   pentagon coherence, and hexagon coherence.
4. Prove any comparison between Rohozhkin/Delaunay flips and the finite
   Fibonacci `F/R/B` matrix readouts.
5. Prove any comparison between boundary defects and Majorana zero modes from a
   BdG/Fredholm/index owner.
6. Prove unitarity/density/universal quantum computation only after a concrete
   Hilbert-space representation and operator-norm statements exist.
