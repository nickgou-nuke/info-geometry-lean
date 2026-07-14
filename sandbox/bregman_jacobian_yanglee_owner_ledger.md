# Bregman / Jacobian / free-energy / Yang--Lee owner ledger

Status: context audit in progress. This ledger records only directly read and compiled source. It is not an exhaustive absence report.

## Search discipline and scope status

Completed exact-source lanes:

- Read and compiled `lean/InfoGeometry/Thermo/ComplexThermodynamicLift.lean`.
- Read and compiled `lean/InfoGeometry/Thermo/FromBregman.lean`.
- Read and compiled `lean/InfoGeometry/Topology/MobiusSouriauThermodynamicFlow.lean`.
- Read and compiled `lean/InfoGeometry/Topology/ThermodynamicSL2MobiusFlow.lean`.
- Read `lean/InfoGeometry/Geometry/LegendreDuality.lean`.
- Read `lean/InfoGeometry/Arithmetic/PrimeGrandCanonicalSouriauBregman.lean`.
- Read `lean/InfoGeometry/Analysis/RotorCocycleBregmanBridge.lean`.
- Read `lean/InfoGeometry/Analysis/BregmanMonodromyBridge.lean`.
- Read `lean/InfoGeometry/Canonical/SouriauOperatorialLogPotential.lean` through line 500 of 630.
- Read `lean/InfoGeometry/ModularVolumePotential.lean`.
- Read `lean/InfoGeometry/Topology/BregmanDivergence.lean`.
- Exact-symbol searched `lean/`, repo-local `agent_writes_recovery`, `sandbox`, `handover/injections`, and `tools/multisystem/major_restore_non_overwriting`.
- Searched Git history for `twoPhasePartition`, `boltzmannLogJacobianEntropy`, and both relevant owner paths.
- Searched the Hermes session DB for exact SL2/Jacobian symbols.
- Audited selected theorem dependencies with `#print axioms`.
- Ran semantic/formula searches for Fenchel gaps, primal/dual Bregman divergences,
  energy-minus-temperature-times-entropy identities, determinant/log-volume
  potentials, Jacobian cocycles, and finite Gibbs normalization.
- Read `Potential/Thermo.lean`, `Algebraic/CartanExponentialFamily.lean`,
  `Thermodynamics/FiniteGibbsRelative.lean`, and `Thermo/FromLogDet.lean`.
- Searched `agent_writes_recovery_v4` and `agent_memory_recovery_stitched` by
  mathematical terminology and formula fragments rather than guessed names.

Incomplete lanes:

- Broad live lexical search returned 500 files and truncated. No global absence claim is licensed by it.
- Monolithic filesystem inventory timed out after five minutes.
- Three delegated ten-minute inventory workers timed out without final artifacts.
- Full recovery/agent transcript scanner remains a separate long-running lane.
- External-reference and generated-index audit is not yet complete.

## Confirmed owners and theorem strength

### Complex two-phase algebra

Owner: `lean/InfoGeometry/Thermo/ComplexThermodynamicLift.lean:267-369`.

Directly read declarations:

- `freeEnergyGap`
- `twoPhasePartition`
- `twoPhasePartition_factor`
- `twoPhasePartition_eq_zero_iff`
- `yangLeeZero_freeEnergyGap`
- `yangLeeZero_realPhaseConditions`

Strength classification:

- These are finite complex algebraic definitions and kernel-checked theorems.
- `yangLeeZero_freeEnergyGap` derives the odd integer exponential phase.
- `yangLeeZero_realPhaseConditions` derives equal real parts and the odd imaginary phase for real nonzero inverse temperature.
- These declarations do not by themselves establish a thermodynamic limit, zero condensation, nonanalyticity, or a zeta-zero identification.

Provenance:

- Git commit `41fb3b9bd` contains an earlier version of this owner without the two-phase section.
- The current working tree adds the direct Cayley section and the complete two-phase section while removing an older bundled `ComplexThermodynamicLiftOwnerTarget` proposition.
- The current file compiles.
- Exact theorem dependency audit reports only `propext`, `Classical.choice`, and `Quot.sound`.

### Finite Bregman-to-Gibbs/free-energy construction

Owner: `lean/InfoGeometry/Thermo/FromBregman.lean`.

Directly read declarations include:

- `energyFromBregman`
- `gibbsProbFromBregman`
- `freeEnergyFromBregman`
- `partitionDivergence`
- `freeEnergyDivergence`
- `partitionDivergence_eq_Z`
- `partitionDivergence_pos`
- `gibbsProbFromBregman_sum_one`
- `freeEnergyDivergence_eq_freeEnergyFromBregman`
- `freeEnergyFromBregman_eq_internal_sub_scale_entropy`
- `KL_param_eq_bregman_energy`

Strength classification:

- This is a genuine finite construction over a `Fintype` using the repository's `LegendrePotential` and finite Gibbs owner.
- The internal-energy/entropy identity requires `epsilon != 0`.
- It does not identify an arbitrary Möbius Jacobian log norm with a Bregman divergence.

The owner compiles. The selected free-energy theorem depends only on standard Mathlib foundations.

### Finite Möbius/Souriau thermodynamic invariance

Owner: `lean/InfoGeometry/Topology/MobiusSouriauThermodynamicFlow.lean`.

Directly read content:

- finite state relabeling of energy;
- partition, Gibbs-weight, mean-energy, Boltzmann-entropy, Massieu, and free-energy invariance;
- chart-realized Möbius permutation and invariant-potential packet;
- metriplectic entropy channel projections.

Strength classification:

- The thermodynamic equalities are finite permutation invariance statements.
- `RealizesFiniteOrbit` and potential invariance are explicit hypotheses.
- This owner does not identify the spatial Möbius Jacobian with a Gibbs density or Bregman energy.

The owner compiles. Its selected packet depends only on standard Mathlib foundations.

### Untracked SL2 finite flow and Jacobian corridor

Current path: `lean/InfoGeometry/Topology/ThermodynamicSL2MobiusFlow.lean`.

Git state/provenance:

- The complete file is untracked relative to `HEAD`.
- `git log --all --follow` returned no history for the path.
- Exact session search returned no matching transcript.
- Exact searches in the checked repo-local recovery lanes found no matching SL2/Jacobian declaration text.
- Therefore this ledger does not classify the file as recovered canonical code.

Directly read declarations include:

- trace-zero generator and matrix exponential flow;
- finite affine Möbius orbit and Riccati ODE;
- spatial Jacobian and multiplicative cocycle;
- additive real log-Jacobian cocycle;
- real-time logarithmic derivative;
- `boltzmannLogJacobianEntropy`, its cocycle, and its real-time derivative.

Strength classification:

- The Jacobian/log-Jacobian statements are concrete algebraic/calculus theorems under explicit affine-chart nonvanishing hypotheses.
- `boltzmannLogJacobianEntropy` is definitionally `kB * logJacobianNorm`; the entropy naming adds no Gibbs normalization theorem.
- No theorem in this file identifies this local quantity with the finite Bregman free energy or with the complex two-phase partition owner.

The file compiles with four style warnings. Selected theorems depend only on standard Mathlib foundations.

### Other inspected surfaces

`lean/InfoGeometry/Geometry/LegendreDuality.lean`:

- general normed-space Fenchel support, conjugacy/majorization, Fenchel gap, nonnegativity, and equality/contact results;
- concrete `fderiv` readouts require explicit dual-value assumptions.

`lean/InfoGeometry/Canonical/SouriauOperatorialLogPotential.lean`:

- mixes theorem projections with structures whose laws are carried as fields;
- contains `RegularizedJacobianPotential`, operatorial exponential-family packets, Souriau negative-log-density data, and `SouriauKLBregmanWitness`;
- several displayed equalities are projections or definitional readbacks, not independent constructions of the analytic objects.

`lean/InfoGeometry/ModularVolumePotential.lean`:

- explicitly declares itself a structural packet surface;
- free-energy, modular-flow, and comparison content is frequently supplied as structure fields or proposition carriers.

`lean/InfoGeometry/Analysis/RotorCocycleBregmanBridge.lean`:

- re-exports finite identities and explicitly records residue/CPT/anomaly statements as open debt.

`lean/InfoGeometry/Analysis/BregmanMonodromyBridge.lean`:

- proves finite matrix/Jordan-block and explicit error-shift identities;
- explicitly states that principal-branch `Complex.log` cannot provide the universal-cover monodromy theorem.

### Finite log-det/Burg-to-Gibbs/free-energy construction

Owner: `lean/InfoGeometry/Thermo/FromLogDet.lean`.

This owner defines `energyFromLogDet` pointwise from the SPD `logDetBregman`
owner, then constructs a finite Gibbs probability, partition, and free energy.
It proves positivity/nonvanishing, normalization, and
`freeEnergyFromLogDet_eq_internal_sub_scale_entropy` (plus a positive-scale
form). This is the existing theorem-honest geometric free-energy lane.

The source explicitly distinguishes its finite statistical partition sum from
the determinant-volume cocycle `det (exp A)`. A raw Möbius Jacobian or its log
norm is not an `SPD n` datum and is not identified with `energyFromLogDet`.
Git history traces this module from its initial geometry-module introduction to
later theorem-native strengthening. `Canonical/RedLine.lean` and
`Canonical/Rosetta.lean` re-export it, so it is not an orphan owner.

### Legendre/Fenchel owner discovered semantically

Owner: `lean/InfoGeometry/Potential/Thermo.lean`.

The actual API includes `LegendreModel.fenchelGap`, `primalBregman`,
`dualBregman`, `canonicalEnergy`, `canonicalEntropy`, `canonicalFreeEnergy`, and
`temperatureRegularizedHamiltonian`. Thus absence of the guessed phrase
`dualBregmanEnergy` was never evidence of missing functionality. The owner proves
contact balance, canonical energy/entropy decompositions, gap nonnegativity and
contact vanishing, and the primal-Bregman/Fenchel bridge under an explicit
gradient/derivative hypothesis.

### Statistical/log-volume separation theorem

Owners: `lean/InfoGeometry/Thermodynamics/FiniteGibbsRelative.lean` and
`lean/InfoGeometry/Algebraic/CartanExponentialFamily.lean`.

The finite Massieu potential is `log (sum exp theta_i)`, while the Weyl/log-volume
readout is `sum theta_i`. The concrete `Fin 2` theorem
`massieuPotential_zero_fin_two_ne_volumeCocycleLog_zero` proves that they are not
interchangeable even at the symmetric point. This is a hard firewall against
identifying an additive determinant/Jacobian cocycle with statistical free energy
without an additional model-level construction.

## Duplication decision already established

The finite complex free-energy/two-phase declarations do not belong in the untracked SL2 owner because the complete stronger owner already exists in `ComplexThermodynamicLift`. The duplicate declarations are absent from the current SL2 file.

## Integration gate

No Bregman--Jacobian--Yang--Lee bridge should be added until all of the following are available:

1. a current owner-level theorem or explicit hypothesis identifying a chosen Möbius Jacobian-derived scalar with the chosen Legendre/Bregman energy or potential;
2. an explicit finite state space and map into `FromBregman`'s `energyFromBregman`, or a separate mathematically justified continuous owner;
3. a typed bridge from that real finite Gibbs/free-energy owner to `ComplexThermodynamicLift.twoPhasePartition`;
4. provenance classification of the untracked SL2 owner against the remaining recovery/archive lanes;
5. downstream import/use audit after any proposed integration.

Until then, the exact open issue is owner integration, not missing elementary two-phase algebra.

## Current integration decision after semantic search

Do not add an SL2-local equality between a Jacobian-derived scalar and Bregman
energy minus temperature-scaled entropy. The correctly typed finite geometric
construction already exists in `Thermo/FromLogDet.lean` and deliberately routes
through SPD Burg energy plus a finite Gibbs ensemble. A future SL2 connection
must first construct an explicit map from Möbius flow/Jacobian data into that SPD
finite-state owner (or a separately justified continuous owner). A shared
logarithm or determinant-shaped formula is insufficient.

## Agent-transcript and Git provenance closure

### Rotor packet

`Analysis/RotorCocycleBregmanBridge.lean` has committed provenance. Its original
June version contained prose asserting, without Lean declarations, rotor/Bregman
identity, particle/hole cancellation, a beta-equals-one phase transition, and
anomaly cancellation. The June 28 audit replaced those unsupported assertions
with kernel-checked forwarding theorems and an explicit open-debt marker.
Therefore the audit removed overclaiming, not theorem-bearing code.

### Möbius owners

`Topology/MobiusSouriauThermodynamicFlow.lean` and
`Topology/ThermodynamicSL2MobiusFlow.lean` have no committed Git ancestors; both
are staged additions. No repository recovery directory contains another copy.
Their provenance is the Pi/Codex transcript
`~/.pi/agent/sessions/--home-goutev-repos-info-geometry-lean--/2026-07-05T14-43-10-630Z_019f32bb-b6a6-77a8-baf7-637418047d77.jsonl`.

The transcript records incremental, repeatedly compiled construction of:

- determinant-one matrix flow and additive one-parameter law;
- affine Möbius orbit and autonomous Riccati ODE;
- denominator owner and chart-validity propagation;
- spatial Jacobian derivative and multiplicative cocycle;
- branch-free logarithmic derivative and principal-log-chart derivative;
- additive real log-norm cocycle and real-time production law.

Every theorem-bearing item from the final transcript state is present in the
staged owner. The transcript also records a temporary duplication of
`freeEnergyGap`/two-phase Yang--Lee declarations in the topology file. Those were
removed after discovering `Thermo/ComplexThermodynamicLift.lean`; the staged
topology owner is the corrected post-dedup version.

No matching Antigravity recovery artifact was found. Codex search hits refer to
status snapshots rather than a competing file body. Consequently there is no
evidence of a stronger deleted Jacobian-to-Bregman/free-energy theorem in these
agent stores.
