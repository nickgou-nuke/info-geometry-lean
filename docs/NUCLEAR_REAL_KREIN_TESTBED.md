# Real dual Krein configuration testbed

## Intake and exact scope

The requested extension consists of a real dual carrier and paired configuration
projection within a fixed physical sector, a constructed complementary inverse on a real energy domain,
Krein-compatible Feshbach elimination, consistently normalized real transition
operators at two endpoints, and joint energy/transition identifiability.
The scalar field is `ℝ` throughout the new declarations. No scalar extension
is part of this construction.

This is a finite configuration representation of the existing operator
identities. It neither replaces the countable CAR/phonon carrier nor supplies
an inverse for that carrier. Nuclear configuration assignments and a
calibrated physical multipole operator remain separate model inputs.
The projector here is the configuration P/Q split inside an already selected
spin/parity sector; the existing `NuclearSymmetrySectors` owner controls
physical-sector support. The present theorem does not derive a spin or parity
assignment for these three basis vectors.

## Ground-truth theorem contract

### Carriers and conventions

Use `EuclideanSpace ℝ (Fin 3)` for the configuration space and
`EuclideanSpace ℝ (Fin 2)` for the retained coordinates. Their native doubled
carriers are `InfoGeometry.Krein.DoubledSpace`, with fundamental symmetry
`spectral_epsilon`, exchange `modular_j`, and internal real phase `clockAxis`.
The literal primal/dual carrier is the existing
`NeutralPhaseSpaceCore.PhaseSpaceCarrier E = E × Module.Dual ℝ E`.
Its metric-preserving realization is the existing
`NeutralPhaseSpaceDoubledBridge.realizedDoubledRhoEquiv`, using the existing
finite Riesz equivalence. Configuration projection retains both doubled legs.

The real configuration matrix, with two retained coordinates and one omitted coordinate, is
`h(a,c,g) = [[a,0,g],[0,a,g],[g,g,c]]`. The model projection is
`p = diag(1,1,0)`. The full doubled operators are paired lifts of these actual
continuous linear maps. The signed metric is not spatial parity, and its two
legs are not the Feshbach P/Q split.

### Owner declarations reused

- `NuclearFeshbachReduction.denominator P H E` is
  `E • (1-P) - (1-P)*H*(1-P)`.
- `NuclearFeshbachReduction.effectiveHamiltonian P H R` is
  `P*H*P + P*H*R*H*P`.
- `NuclearFeshbachReduction.waveOperator P H R` is `P + R*H*P`.
- `residual_identity` and `eigen_equation_iff` use supported right inversion;
  `reconstruct_eigenvector` uses the supported left inverse.
- `NuclearFeshbachSymmetry.cornerInverse_unique` proves uniqueness from both
  corner identities, without assuming ambient invertibility.
- `KreinSpace.kreinAdjoint A = eta ∘ A.adjoint ∘ eta` owns the real indefinite
  endomorphism adjoint. Its multiplication and involution laws are reused.
- `NuclearEffectiveObservables.effectiveOperator Ωi Ωf O = Ωf.adjoint ∘ O ∘ Ωi`;
  `metricWeight_eq_norm_sq` and `normalized_transition_strength` transport
  the exact positive normalization, specialized at `ℝ`.
- `BornRuleCore.kreinInner_fundamentalSymmetry_right` identifies the positive
  real pairing with `[u, eta v]` in the same Krein carrier.

### Concrete inverse and real domain

Prove `QHQ = c Q` for the actual model. Set `R(E) = (E-c)⁻¹ • Q`.
For `E != c`, prove `QR = RQ = R` and `DR = RD = Q` explicitly. Under `a<c`,
the open real interval `E < (a+c)/2` avoids the complementary pole. Prove
real analyticity and an explicit uniform bound on this interval using native
Mathlib analysis, rather than assuming a resolvent field in a structure.

The graph map is the actual continuous linear map
`omega(E)(x,y) = (x,y,g*(x+y)/(E-c))`. Prove its correspondence with the owned
Feshbach wave operator, injectivity, and normalization. The paired graph uses
the same map on both native doubled legs.

### Joint readout contract

Use the explicit real probe `O(k) = k * diag(1,-1,0)`, with `k != 0`.
The dark model vector is `(1,-1)` and the bright model vector is `(1,1)`.
Their reconstructed full states are `(1,-1,0)` at energy `a` and
`(1,1,2*g/(E-c))` at energy `E`. Both doubled states use the same specified
positive native leg. The observable is lifted to both legs, and the two wave
maps retain their distinct energy arguments.

Derive the scalar strength from the actual normalized operator amplitude;
do not insert its formula as an assumed observation law. Under `a<c`, `g!=0`,
`E<(a+c)/2`, and the actual bright eigen-equation, derive
`(a-E)*(c-E)=2*g^2`, `E<a`, and
`B=k^2*(c-E)/((c-E)+(a-E))`. Recover

`c = E + (a-E)*B/(k^2-B)` and
`g^2 = (a-E)^2*B/(2*(k^2-B))`.

The conclusion identifies `c` and `g` up to sign. The sign ambiguity is
represented by the actual omitted-coordinate sign-change conjugacy of the Hamiltonian.
The rational case `a=2,c=3,g=1,E=1,k=1` supplies a nontrivial instance with
nonzero off-block coupling and strength `2/3`.

### Excluded stronger claims

The calibrated probe is not asserted to be a derived nuclear E2/M1 operator.
The normalized squared amplitude does not include an automatically supplied
spin reduction factor, phase-space factor, detector efficiency, or branching
correction. No experimental dataset is fitted. No infinite-dimensional domain,
colimit inverse, nuclear chirality assignment, or full many-body representation
is inferred from the finite identities.

## Implemented interfaces

The import entrypoint is `InfoGeometry.Physics.NuclearRealKreinTestbed`.

| Requested part | Native owners and principal results |
| --- | --- |
| Real dual carrier and retained projector | `NuclearDoubledConfiguration.pairedLift`; `NuclearThreeConfigurationDual.dualRealization_intertwines`, `dualRealization_pairing`, `doubledProjection_preserves_duality`, `doubledProjection_nondegenerate` |
| Constructed inverse and real domain | `NuclearThreeConfigurationResolvent.denominator_mul_resolvent_eq_complement_iff`; `NuclearThreeConfigurationKreinReduction.doubled_corner_inverse`; `NuclearThreeConfigurationDoubledAnalytic.analyticOnNhd_doubledResolvent_validityWindow` and its uniform norm bound |
| Native Krein reduction | `NuclearRealKreinFeshbach.resolvent_kreinAdjoint`, `reconstruct_eigenvector`; `NuclearThreeConfigurationKreinReduction.doubled_effectiveHamiltonian_kreinSelfAdjoint`, `doubledGraphMap_eigen_equation_iff` |
| Effective transitions and normalization | `NuclearRealKreinObservables` for rectangular Krein adjoints and positive Gram transport; `NuclearRealClockTransitionStrength` for independent real clock rotations; `NuclearThreeConfigurationDoubledTransition.clockMeasuredStrength_eq`; entrypoint `normalized_dark_norm`, `normalized_bright_norm` |
| Joint observations | `NuclearThreeConfigurationInference.measuredStrength_bounds`; entrypoint `doubled_recover_parameters`, `doubled_joint_identifiability`; `NuclearThreeConfigurationWitness.signGauge_hamiltonian`, `example_coupling_nonzero` |

`NuclearThreeConfigurationAnalytic` also proves real analyticity of both
configuration and doubled graph embeddings, their positive Gram operators,
and the actual rectangular effective observable. In particular,
`analyticOnNhd_twoEndpoint_doubledEffectiveOperator` uses independent
`ci, gi, cf, gf` and the open domain

`{(Ei, Ef) : R x R | Ei != ci and Ef != cf}`.

The `NuclearRealKreinComplementaryResolvent` adapter additionally connects an
actual native equivalence on `ker P` to the existing algebraic inverse owner.
The concrete testbed constructs its inverse directly and proves both corner
equations; it does not assume such an equivalence as an input.

### Parameters and observable quantities

| Quantity | Role in the theorem |
| --- | --- |
| `a, c, g` | Parameters of the actual real three-configuration Hamiltonian |
| `a, E` | The dark eigenenergy and lower bright eigenenergy supplied to the inverse observation map |
| `kappa` | Known nonzero calibration of the specified transition operator |
| `B` | Derived normalized matrix-element strength, including both induced Gram factors; on the doubled carrier it equals the two-quadrature readout |
| `c, g^2` | Uniquely recovered quantities; the real basis change leaves the sign of `g` undetermined |

For `a=2, c=3, g=1, E=1, kappa=1`, the reconstructed states are
`(1,-1,0)` and `(1,1,-1)`. Their squared positive norms are `2` and `3`,
the unnormalized matrix element is `2`, and the proved normalized strength
is `2/3`. The model/complement coupling is proved nonzero.

Both external states are initially specified on the same positive native
leg. The two-quadrature observable is invariant under independent endpoint
clock rotations when the probe intertwines the clock axis, as the paired
probe does. This remains a real operator statement. The signed indefinite
norm is never used as a probability denominator.

The dual action `A` on the primal leg and `A.dualMap` on the covector leg is
intertwined with the paired realization under `A.adjoint = A`. It is not
claimed to preserve arbitrary noncommuting products; the Feshbach products
are formed in the actual bounded paired-operator algebra.

## Verification record

Validation completed on 2026-10-26, against parent commit
`aed2e4496cb1bb05a1f72b75538f660b4803b2c5`.

- The author and independent QA-A both built
  `InfoGeometry.Physics.NuclearRealKreinTestbed` successfully under the native
  shared build lock: 3588 Lake jobs in the targeted source graph.
- The checker imports the actual repository `lean/` sources and uses the
  unchanged pinned Lean 4.34.1 and Mathlib revision
  `d13f23b723b8a846827a245b89c10fc7d3f11612`. No compiler preload, dependency
  override, or alternative mathematical implementation was used.
- Independent exact-byte direct elaboration passed for all 16 new Lean files.
  The final two-file proof-only correction received another exact-source check;
  the other 14 files were retained by verified byte equality. The umbrella
  and all public axiom reports were checked again after that correction.
- The inventory contains 195 public theorems, 39 public definitions, and five
  public abbreviations: 239 public declarations. Six private theorem helpers
  were also compiled in the exact-source checks and are covered transitively
  where used by the public declarations.
- Every public declaration received an independent `#print axioms` report.
  Their combined dependencies are exactly `propext`, `Classical.choice`, and
  `Quot.sound`. There are no custom axioms, `sorryAx`, admitted proofs, unsafe
  declarations, or native decision shortcuts in the checked payload.
- Placeholder, whitespace, staged proof-proxy, OpenGauss screener, strict
  refutation, static Gate 4, and semantic-vacuity checks pass. The 17 lexical
  trivial-surface notices were independently reviewed as native interface
  readouts and elementary proved identities. No semantic blocker remains.
- Four initial strict-refuter unused-binder notices concerned three contextual
  `linarith` calls. Those calls now name their existing inputs explicitly;
  statements, hypotheses, and conclusions are unchanged. The strict rerun is
  clear. No warning was suppressed or gate configuration relaxed.
- Direct source checks retain 54 nonfatal compiler lint warnings: 29 redundant
  section-variable inclusions, 13 sequence-focus suggestions, six unused simp
  arguments, three unreachable tactic notices, and three unused tactic notices.
  Existing dependency lints also remain. This is not a warning-free build claim.
- The independent mathematical A-A review and independent QA-A acceptance were
  performed by separate agents with no theorem authorship in those roles.
  Final proof-file hashes were stable throughout acceptance.
- The prescribed repository-root build was retried and fails before target
  compilation because `external_refs/atlas-lean` is absent. These results are
  targeted source/kernel validation, not whole-repository or remote-CI
  certification. Existing owners, dependency manifests, and pins are unchanged.

### Accepted proof-file identities

Paths below are relative to `lean/InfoGeometry/Physics/`.

| Lean file | SHA-256 |
| --- | --- |
| `NuclearDoubledConfiguration.lean` | `cc0a16003fbec23233af7121cc429eb67d1525f32f77bfa9423b12bc232d7c29` |
| `NuclearRealClockTransitionStrength.lean` | `a7d4dfca39e9bc9aedc5ac9f9fb92957580926a2c04f7038a71346cd32ac8472` |
| `NuclearRealKreinComplementaryResolvent.lean` | `27647092504a387a0a09f515b1a400c5b175dc2bb54081b005758a64f07c8455` |
| `NuclearRealKreinFeshbach.lean` | `a6a85ca445e344485bd1de92c5cf0bf49d8c949afca56ba026af9dfcdf75952f` |
| `NuclearRealKreinObservables.lean` | `060cfe5d18b87897713b14c4f4eb35593085fa5c9d9b5e3b9122c48235a898c9` |
| `NuclearRealKreinTestbed.lean` | `96895925b58470fda1001dacb69e360d08f3c6a6df8cb154437412b78d94d509` |
| `NuclearThreeConfiguration.lean` | `58fd48def05ea7242f22edac7cc2c9de9403a98af14436f05ade51d913d6af0c` |
| `NuclearThreeConfigurationAnalytic.lean` | `925933c2350712bdeaa36ad7a5943fd3bbb7e0913088e010e135d60a3ed6cf1c` |
| `NuclearThreeConfigurationDoubledAnalytic.lean` | `4b4f0ab31c0cf6052f957060c35e94db7eb3aec4110e9168e929f142ab7b525e` |
| `NuclearThreeConfigurationDoubledTransition.lean` | `b4dcef3e3e6938179b00dded36a49f14351030086dd82f8f2dd706a5e97b00c3` |
| `NuclearThreeConfigurationDual.lean` | `4400efa0ccbf88df9d3445236f1a6441d05995e5a76b5198f97f3fb29d261080` |
| `NuclearThreeConfigurationInference.lean` | `7a4c56a4820b689ca9111378a1c9e83a93366130ae55aa1bb6edc4feab0431ff` |
| `NuclearThreeConfigurationKreinReduction.lean` | `2f572e7763d8568a7b832e5b3a48ddebd0b4c660691b339d5f407eac8d8cfa33` |
| `NuclearThreeConfigurationResolvent.lean` | `1ddefe038284f221a447f8c7b1e3c2a7efa05fa83abc611cda9b252da59aba8d` |
| `NuclearThreeConfigurationTransition.lean` | `dd5dcb9775f7a631728d3651b262783cf9b009adcf60e81ecdd4bb914fe7b3ac` |
| `NuclearThreeConfigurationWitness.lean` | `e230513863c569a0794785db82ef75c0c4bda6ceee3ac77cd6b88ff5c651ddb2` |
