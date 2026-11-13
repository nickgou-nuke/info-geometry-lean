# Noncommutative Clifford coordinates and Peirce affinity

## Intake and scope

This continuation receives two user attachments, preserved unchanged in the
conversation: `Pasted text(20261112-173925).txt` (Clifford, curvature, Peirce,
and star-form blocks) and `Pasted text (2)(2).txt` (affinity, lower masks,
and ordered coefficient convolution). The pasted Lean is candidate input,
not compilation evidence. The task is implementation on existing owners in
native Mathlib, with arbitrary noncommutative coefficient rings retained.

Source baseline: `a392af178af1fe2bcba2ba39eb405700c6ee103c`.
Lean: `v4.34.1`. Mathlib: `d13f23b723b8a846827a245b89c10fc7d3f11612`.
Dependency pins and verification configuration are not changed.

Input SHA-256 digests:

* First attachment: `b91f747c5cf2a9a6cb9d05dc6aff5f760072e1a64a7579e0c90d59d59dd8c5ed`.
* Second attachment: `2c7c6ae0156acb279928bc334c82e387a2e051c73a8875941a10519d46657260`.

The previous uncommitted `formal/dewitt-brst-morita` working tree did not
survive the runtime reset and was not found upstream. Its earlier static
review is not acceptance evidence for this checkout. This intake does not
close the earlier D-dimensional DeWitt, BRST cohomology, direct-limit Morita,
or physical mass obligations by renaming finite Peirce identities.

## Claim inventory and corrections

| Intake claim | Exact mathematical contract |
|---|---|
| Non-Abelian covariant derivative | Reuse the existing regular-module connection and curvature owners; `D + a·` is generally not itself a derivation. |
| Four Clifford operators form a basis over every ring | False without a hypothesis on two. Unconditional coefficient synthesis returns `M + M`. Right normalization constructs a left-module linear equivalence over the coefficient ring itself when two is invertible. |
| `Cl(1,1)` tensor factorization over the integers | The displayed integral matrices generate a proper parity order. Existing integral-order owners already state this obstruction. No unconstructed universal Clifford/tensor equivalence is asserted. |
| Operator-valued Weyl braid | Prove the ordered two-by-two identity and shift inversion for units, without claiming `diag(u,u⁻¹)` is a homomorphism on noncommuting units. |
| Internal square root of minus one | Conditional matrix-square and anticommutation statements for a supplied `j*j = -1`; no centrality or external complex scalar. |
| DeWitt even/odd split | Reuse the existing Peirce grading. It is a ring grading, not a quadratic signature or Witt theorem. |
| Mellin-Walsh transform | A finite additive coefficient transform relative to the existing Clifford frame. No analytic Mellin integral or spectral theorem. |
| Symplectic Lie algebra and squeeze group | Construct native LieSubalgebra/Subgroup objects from an actual star-form preservation equation, prove block classification, and construct the unit squeeze homomorphism. |
| Hermitian/skew affinity decomposition | An ordered star pairing and doubled self/skew sum; no polar decomposition or positivity claim. |
| Causal mask | An additive idempotent projection onto an existing native lower-support subring. No temporal order, multiplicative projection, or star-closed image is assumed. |
| Index-two nilpotency | Square-zero of the individual off-diagonal corners; exact nilpotency index two would additionally require nonzero input. |
| Attention convolution | An exact product formula with all coefficient factors ordered. Doubled inputs give four times the product; no softmax or nonlinear attention semantics. |

## Reused source owners

* `Geometry/AssociativeGaugeConnection.lean`: `IsLeibniz`,
  `covariantDerivative`, `connection_leibniz`, `curvature_action`, and
  `curvature_gauge_covariant` on actual linear endomorphisms.
* `OperatorAlgebra/DerivationGaugeTransport.lean`:
  `fundamentalCovariantDerivative_commutator_eq`, including the Lie-direction
  correction, and exact gauge transport. This stronger surface already
  exists and is not duplicated here.
* `Clifford/OperatorValuedJones.lean`: `I_mat`, `Gamma_mat`, `J_mat`,
  `K_mat`, `reconstruct_jones`, and `jones_decomposition_eq`. The intake's
  skew generator is `-K_mat`; all new sign conventions must record this.
* `Algebra/IntegralChiralCliffordOrder.lean` and its canonical companion:
  the integral parity subring, its properness, and rational spanning.
* `Algebra/MatrixNoncommutativity.lean`: the actual noncommuting full
  two-by-two matrix pair over every nontrivial coefficient ring, including
  characteristic two. The three matrix owners explicitly import this exact
  carrier witness; the existing Jones witness over complex matrices alone
  does not supply that generic carrier evidence.
* `OperatorAlgebra/PeirceHadamardNative.lean`: the existing distinction
  between an unnormalized Walsh identity and a unit under invertible two.
* `Algebra/IdempotentProjector.lean`, `PeirceDeWittChiralSplit.lean`,
  and `PeirceParityClosure.lean`: generic four-corner and parity identities.
* `OperatorAlgebra/PeirceSpine/Basic.lean` and `StarGrading.lean`:
  the existing `conePlus`, `coneMinus`, `evenGrade`, `oddGrade`, their
  product/projection laws, star reversal, and `digracSym`/`digracImb`.
* `OperatorAlgebra/ThreeCornerColumnAlgebra.lean`: `supportedSubring`
  and finite-product closure. The specialization at idempotents `(0,p)`
  is the lower-support subring; its concrete membership characterization
  is part of the new bridge.

The search covered filenames and declaration contents in the canonical
`lean/` tree, related `src/` copies, relevant imported owners and consumers,
and the categorical infrastructure map. The map is navigation evidence;
its interpretation labels are not additional theorem hypotheses or proofs.

## Construction contracts

### Ordered Clifford coordinates

For `Matrix (Fin 2) (Fin 2) A` over `[Ring A]`, extract the four entries
`(M00+M11, M00-M11, M01+M10, M10-M01)` and synthesize them with the existing
Jones frame `(I,Gamma,J,-K)`. Prove both round trips equal doubling, then
construct the normalized native left-module linear equivalence under explicit
invertibility of two in the coefficient ring. Right normalization retains
left linearity without commuting coefficient products. Use `Matrix.scalar` for coefficient embeddings;
these embeddings need not commute with each other. Prove the full ordered
four-component multiplication law and star duality. Connect the entry
extraction with the Peirce fiber formula, rather than merely assigning it the
same name. New modules may import the existing Jones owner despite its broad
historical tactic import; new direct Mathlib imports remain focused.

### Star forms and two-by-two units

For a star ring `B` and actual form element `j`, build the native subgroup
of units with `star u * j * u = j`, and the native integer Lie subalgebra
with `star x * j + j * x = 0`. Derive closure from the ring/star laws.
Specialize to the existing two-by-two skew generator, prove the precise
Hamiltonian block characterization, and construct
`u ↦ diag(u, star(u⁻¹))` as a monoid homomorphism into preserving units.
The two order reversals are necessary to this multiplication law.

### Peirce affinity and lower projection

For arbitrary `[Ring B] [StarRing B]`, define the ordered pairing
`q * star k` and its form-twisted version. Prove star swap, outer-factor
covariance, biorthogonal invariance, and form-congruence invariance.
Use a self-adjoint idempotent for star-compatible Peirce factorization.
Construct the additive lower projection `x - conePlus p x`, characterize
its fixed points and range by the existing `supportedSubring` at `(0,p)`,
and inherit multiplication/power closure from that native subring.

### Explicit matrix specializations

Supply the actual squeeze preservation equation to the generic affinity
transport theorem, and instantiate coefficient convolution at matrix
products. Matrix entries remain arbitrary operators. Neither preservation
nor reconstruction is assumed as a field of a task-specific structure.

## Dependency order

The ring/star laws feed independent branches: existing connections and
curvature; existing Peirce projections and lower-support subring; existing
Jones frame and finite coefficient convolution; star-form preservation and
squeeze homomorphism. Pairing factorization depends on Peirce and star laws.
Squeeze invariance depends on the constructed preserving unit. Convolution
does not depend on squeeze, star, a DeWitt signature, or a BRST complex.

## Native owners and decisive declarations

All paths below are relative to `lean/InfoGeometry/`.

| Owner | Constructed object and decisive proofs |
|---|---|
| `Clifford/OperatorCliffordWalsh.lean` | Additive `coefficients` and `synthesis`; both doubling round trips; `peirceFiber_eq_scalar` and four extraction bridges; ordered `synthesis_convolution` and `convolution_coefficients`; `coordinateEquiv : Matrix (Fin 2) (Fin 2) A ≃ₗ[A] (Fin 4 → A)` under `[Invertible (2 : A)]`; exact normalized product transport. |
| `OperatorAlgebra/StarFormPreservation.lean` | `preservingSubgroup : Subgroup Bˣ`; `infinitesimalLieSubalgebra : LieSubalgebra ℤ B`; unit inverse and multiplication closure, integer linear closure, and actual commutator closure. |
| `OperatorAlgebra/StarSymplecticBlocks.lean` | Reciprocal diagonal units and ordered Weyl braid; internal-coefficient square and anticommutation laws; full `mem_infinitesimal_iff` and Hamiltonian block classification; injective `squeezeHom` into the preserving subgroup; shifted biorthogonal partner. |
| `OperatorAlgebra/PeirceAffinity.lean` | Ordered star pairing and doubled self/skew decomposition; star-compatible Peirce factorization; biorthogonal and form-congruence transport with explicit equations. |
| `OperatorAlgebra/PeirceLowerProjection.lean` | Existing native subring specialization, exact upper-corner-zero characterization, additive projection and surjective retraction, equality of additive range with the subring carrier, finite product closure. |
| `OperatorAlgebra/MatrixPeirceAffinity.lean` | Full matrix specializations discharge transport hypotheses using the constructed units; raw and normalized affinity convolution; canonical lower entry mask and a nonmultiplicativity witness using `E01 * E10`. |

The ring-only declarations retain arbitrary `[Ring A]`. Star-dependent
declarations add `[StarRing A]`. The Peirce projection requires an actual
idempotent, and star-compatible factorization additionally requires it to be
self-adjoint. The nonmultiplicativity inequality uses `[Nontrivial A]`.
Neither normalized coordinates nor a characteristic restriction is used to
prove the raw product identities.

## Roles and acceptance

The parent writes the coefficient/bridge candidates and integrates reviewed
work. The Clifford and affinity agents author isolated candidates and review
each other's source; the environment/QA agent authors no theorem content.
All compiler, cache, and build processes use the maintained shared-lock
route, with one active lane. Final acceptance requires exact pinned narrow
builds, complete-source placeholder/semantic screening, all-public-declaration
axiom inspection, independent semantic review, and the staged proof gate.
Only the permitted foundational dependencies `propext`, `Classical.choice`,
and `Quot.sound` may appear. Source checks, kernel checks, and publication
gates are reported separately.

## Verified scope

The six new owners passed focused verification on 2026-11-12 with the exact
toolchain and Mathlib pin above:

* The combined `InfoGeometry.OperatorAlgebra.MatrixPeirceAffinity` target and
  its dependency closure built successfully through the maintained focused
  shared-lock wrapper.
* All six new source files passed direct Lean checks with
  `-DwarningAsError=true`; no new-owner warning was emitted. After adding the
  three direct witness imports, the three changed files were rechecked; the
  other three retained byte-identical source and staged-index evidence.
* The complete-source scan found no forbidden proof construct, custom axiom,
  unsafe code, or local linter/kernel override. The maintained source
  screener returned no findings, and all six headers matched policy.
* The generated audit printed axiom dependencies for every one of the **117**
  public named declarations: 26 coordinates, 7 generic star-form, 37 block,
  21 affinity, 18 lower-projection, and 8 matrix-specialization declarations.
  All 117 reports were parsed in the expected order. Their axiom union was
  exactly `propext`, `Classical.choice`, and `Quot.sound`.
* `python3 tools/quality/proof_proxy_staged_gate.py` exited 0 on the staged
  sources. Independent source reviews found no mathematical mismatch with
  the construction contracts.

The dependency build reports five inherited warnings: one in
`OperatorValuedJones`, three in `ThreeCornerColumnAlgebra`, and one in the
existing `MatrixNoncommutativity` witness. These are distinct from the
zero-warning checks of the six new owners. No historical owner, dependency
pin, verification configuration, scanner, hook, or gate was edited.

Reproduction commands, with the pinned Lean executable on `PATH`:

```bash
python3 verification/twistor-hadamard/check.py build \
  InfoGeometry.OperatorAlgebra.MatrixPeirceAffinity
python3 verification/twistor-hadamard/check.py env lean \
  -DwarningAsError=true "$PWD/lean/InfoGeometry/Clifford/OperatorCliffordWalsh.lean"
python3 tools/quality/proof_proxy_staged_gate.py
```

The direct source check is applied separately to each of the six owner paths.
The axiom audit imports all six modules and runs `#print axioms` for every
public declaration extracted by the maintained certification helper.
Exact commands, source/index SHA-256 hashes, parsed dependencies, and logs
are recorded in the task acceptance receipt. The first staged-gate failure
for missing generic witness imports was preserved; the successful recheck
includes the existing exact-carrier witness imports.

This is focused acceptance of these six owners, with the separate publication
result recorded below. Source inspection has identified unresolved root path
dependencies for `HomotopyHypothesis`, `Atlas`, and `GIFT`; focused verification
does not substitute for restoring the intended root dependency snapshots.

## Publication checks and draft review status

The implementation was committed locally as
`7d138642932a5e7694f23e57abec1dd7e5dac702` on
`feat/noncommutative-peirce-affinity`; its tracked pre-commit hook passed.
The ordinary `git push` exited 128 because command-line Git had no GitHub
credentials. The connected GitHub app independently confirmed that the branch
was absent upstream.

The unchanged tracked pre-push hook was then invoked on that exact commit,
with the actual new-ref update and zero remote old SHA. It exited **1**:

* The locked root Lake build failed because
  `external_refs/homotopy-hypothesis-lean4` was absent.
* The six-file source-debt audit passed with zero open gaps.
* The semantic-content audit passed over its 27,020 selected Lean files, with
  zero blocking findings. This is source screening, not compilation of those
  files.
* The tracked Lean scope and quarantined-artifact audits passed.

The hook therefore did not reach its subsequent root gate for a new ref.
That initial attempt created no upstream branch or pull request. The
documentation checkpoint recorded this result and the bounded original-obligation
review; the six verified Lean sources remained unchanged.

After these results were reported, the user explicitly requested upstream PR
publication. The reviewed change is being submitted as a draft, with the failed
root build retained as an unresolved acceptance item. The focused proof checks
and source audits do not certify the root package. Dependency pins, gate behavior,
and historical source owners are unchanged. Restoring or deliberately changing
the root dependency snapshots remains necessary for root-package acceptance;
dependency changes retain the authorization requirement in `AGENTS.md`.

## Boundaries of the earlier three obligations

The following is a bounded source review of nearby existing owners, not a
whole-repository compilation certificate or a claim that all related results
are absent. None of these broader obligations is discharged by the six new
finite algebra owners.

### DeWitt quadratic space

The existing Peirce and trace-expansion owners prove ring identities. Separate
owners such as `Clifford/SplitCliffordFourPlaneWittClosure.lean` construct real
quadratic and split-plane results on a fixed `(4,4)` carrier. The missing target
here is an explicit D-dependent DeWitt quadratic form, its nondegeneracy and
signature, and an actual isometry to the proposed Witt decomposition.

For the proposed signature `(D(D-1)/2,D)`, a decomposition into D hyperbolic
planes requires `D(D-1)/2 >= D`; for positive D this requires `D >= 3`.
The proposed positive complement then has dimension `D(D-3)/2`. Those are
necessary dimensional conditions for the future statement, not consequences
of the Peirce grading proved in this change.

### BRST complex and quotient

`Lie/BRSTCohomology.lean` already defines the correct kernel/comap quotient,
constructs the concrete two-dimensional Nambu differential, proves
`nambu_ker_eq_range`, and proves its quotient trivial. The missing requested
result is the general graded quartet construction with both Q and R, the
number-operator relations, and the cohomology equivalence induced by a proved
contraction. A descended pairing or nullity of exact states additionally does
not construct a positive-definite complete Hilbert quotient.

A separate pre-existing definition requires correction before it can support
that claim: `Canonical/IntegerGradedBRSTCochainComplexBridge.lean` defines
`integerGradedBRSTCohomologyDegree` as the entire next ghost eigenspace modulo
the preceding differential's range. Its comment describes kernel modulo
image, but its actual carrier is a cokernel-style quotient. The source review
records this mismatch; this change does not repair that separate owner or
count its title as cohomology evidence.

### Morita, traces, and geometry

`OperatorAlgebra/PeirceSpine/TripotentGradedMorita.lean` already constructs a
native `MoritaEquivalence` from a nonempty finite basis and lifts the associated
module-category equivalence to the grading action. Separate `Cl11TensorTower`
and limit owners construct stage embeddings and an algebraic direct limit.
What is still needed for the earlier target is the actual equivalence data
for the specified tower/limit carrier and compatibility with those maps;
finite-stage equivalences alone do not provide it.

`Canonical/CyclicTraceIsometryObstruction.lean` already proves the obstruction
with explicit additive trace, cyclicity, one-sided inverse, partition, and
normalization hypotheses. Applying it to the claimed tower requires proving
those hypotheses for the actual representation and trace. It is inaccurate
to describe cyclic-trace obstruction results as entirely absent.

Existing finite twistor mass and internal pitch formulas likewise do not
identify the homotope/skew-tripotent matrices with the proposed physical
twist, spatial pitch, or mass. That interpretation requires its own specified
geometric map and compatibility theorem.
