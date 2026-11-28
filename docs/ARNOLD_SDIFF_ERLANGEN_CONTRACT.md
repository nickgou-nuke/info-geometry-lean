# Arnold–SDiff–Erlangen bridge: theorem contract

## Provenance and source boundary

Intake: [20261128_arnold_sdiff_erlangen.md](intake/20261128_arnold_sdiff_erlangen.md).
The initial implementation used the named smooth measure and Arnold owners
at the published, unmerged PR #474 head
`722d33728a967fddec3187bdac1d17a8df758748`, above the initially observed main
`fe24e350b08fdea04f74c0748ef9fd9417c47529`.

A fresh GitHub check found main at
`e2aa23c786c63c8992e8936346ed5f7782e4e164`. All fourteen Lean owners introduced
by PR #474 and both of its contracts were already present there with identical
Git blobs, although the original two commits were not ancestors. Seven
pre-existing dependencies in the selected closure had changed. This task was
therefore integrated into a separate ordinary checkout at `e2aa23c`, retaining
those upstream changes and rerunning acceptance for that actual source tree.
No old umbrella file or dependency is substituted for its current version.

The intake's background-process note is preserved as supplied context; it is
not evidence of a completed merge or a live push. The previous reductive-shear
PR #477 is a separate change.

Pinned environment: Lean `v4.34.1`, Mathlib
`d13f23b723b8a846827a245b89c10fc7d3f11612`. Neither pin is changed. The compiler
has been restored and the exact Mathlib checkout and all eight dependency
pins are verified. The source-scoped kernel and axiom acceptance is recorded
below; the normal publication gate remains incomplete.

## Exact carriers and intended construction

- `G = smoothDiffeomorphismSubgroup E`, the existing subgroup of `E ≃ₜ E`
  whose maps and inverses are `ContDiff ℝ ∞`, on a real normed vector space.
- Vector fields are functions `E → E`. The pushforward formula makes sense
  for arbitrary such functions because differentiability is required of the
  acting diffeomorphism. Smoothness of a field is a separate predicate.
- Flows in the algebraic action are actual homomorphisms
  `Multiplicative ℝ →* G`. A homomorphism alone does not assert time
  regularity or identify its generator; generator theorems use explicit
  `HasDerivAt` hypotheses.
- Invariant measures use the existing left pushforward action on native
  `Measure E`, with the owner's measurable/Borel assumptions.
- Closure is the native order-theoretic Galois closure on `Subgroup G` for a
  specified observable carrier and action. Algebraic subgroup generation
  uses `Subgroup.closure` separately.
- Quotients are native subgroup coset types, and orbit equivalences are
  equivalences of those types. No quotient-group, manifold, or
  infinite-dimensional Lie-group structure is asserted.

## Owner and Mathlib reuse

| Source | Interface used | Boundary |
| --- | --- | --- |
| `Canonical/SmoothDiffeomorphismDensityOrbit.lean` | smooth group, native measure action, `measure_stabilizer_eq_comap`, `measureOrbitEquivQuotient` | actual orbit, not all densities |
| `Canonical/SmoothVolumePreservingGroup.lean` | `smoothVolumePreservingSubgroup` | includes both smoothness directions and actual `MeasurePreserving` |
| `Canonical/ArnoldBeltramiFlow.lean` | actual real flow, `hasDerivAt_flow`, spatial Fréchet derivative, actual curl/divergence | explicit three-dimensional model |
| `Canonical/ArnoldInformationGeometry.lean` | `smoothFlowHom`, `smoothFlowHom_fixes_volume` | all real parameters; Beltrami curl specialization has its own hypotheses |
| Mathlib `GroupAction/FixingSubgroup` | `fixingSubgroup`, `fixingSubgroup_fixedPoints_gc`, native antitonicity | only `MulAction`, no artificial semiring of measures |
| Mathlib `GroupAction/Quotient` | `orbitEquivQuotientStabilizer` | coset-set equivalence |
| Mathlib Fréchet and scalar derivative owners | derivative of composition, `HasDerivAt` composition and uniqueness | real normed-space calculus under declared hypotheses |
| Mathlib `VectorField` | bracket convention `DW·V - DV·W` | forward pushforward and pullback have opposite infinitesimal signs |

The semiring-specific `OperatorErlangenGaloisConnection` is source context.
The new closure construction uses native general-action Mathlib owners, with
no artificial multiplicative action on densities. It does not directly import
the broader `InvariantGeometry` owner. The concrete Arnold integration still
inherits the existing owner's wider dependency graph, including
`FiniteSpinAlgebra` through `KLScaleItakuraSaito` and `GaugeReduction`; its
complete import closure is not claimed to be complex-free. The new carrier,
pushforward calculus and concrete flow remain real.

The adjacent log-volume owners on current upstream have distinct scopes.
`Canonical/LieFlowLogJacobianBridge.lean`
defines a scalar negative logarithm, its positive-scalar product law, complex
exponential norm readouts, and finite skew-matrix consequences. The separate
`Analysis/LieFlowLogJacobianBridge.lean` defines the log-volume of the actual
finite matrix exponential path and identifies it with `t * Matrix.trace A`.

Unlike the initial `722d3372` checkout, current upstream contains
`Canonical/LieFlowDilatonSymFactorization.lean`. Its
`lieFlowLogJacobian_eq_dilatonPart_symPart` factors that finite matrix readout
through the symmetric pure-trace part when the dimension is nonzero, and
`lieFlowLogJacobian_eq_zero_of_skew` gives skew-generator vanishing. These
statements do not supply a nonlinear diffeomorphism Jacobian cocycle, a
divergence field or a constant-scale group exact sequence.

`Canonical/SouriauCoadjointOrbitBridge.lean` contains abstract dual/KKS
identities and a real Onsager--Casimir response construction under supplied
symmetry and nonnegativity hypotheses for its bilinear metric. It does not
construct the proposed SDiff vorticity orbit or Kelvin dynamics. These
adjacent owners are source context; their stronger geometric identifications
are not premises of the new bridge or part of its selected validation scope.

## Claim ledger and corrections

| Intake claim | Disposition and exact target |
| --- | --- |
| Fréchet pushforward is a group action | prove actual identity/composition laws, then install a scoped native action |
| Conjugation is an action on flow homomorphisms | prove for an arbitrary group, retaining multiplication order |
| Time-zero differentiation intertwines these actions | prove under an explicit derivative hypothesis at every starting point |
| A flow's symmetry subgroup is its centralizer | prove stabilizer of the whole homomorphism equals centralizer of its image |
| Stabilizers transform by conjugation | prove for the actual installed actions |
| Flow symmetry and generator symmetry coincide | forward inclusion is justified by differentiation; converse requires an ODE uniqueness theorem and is not smuggled into an action definition |
| Volume-invariant flows generate SDiff after closure | prove `H ≤ Cl_Measure(H) ≤ Stab(volume)`; equality requires a separate invariant-separation or generation theorem |
| Distribution preservation is a flow/group normalizer or the Lie-symmetry group of an ODE/PDE system | needs a specified distribution or module of fields and a compatibility theorem; preservation of a real linear span alone does not establish that identification |
| Diff ≥ SDiff ≥ contact/symplectic ≥ isometry ≥ flow symmetry | no unconditional chain; form intersections or add compatible invariants and prove each inclusion |
| Jacobian zero set is an ordinary homomorphism kernel | nonlinear Jacobian is a cocycle; a stabilizer need not be normal |
| SDiff is exactly determinant-one maps | orientation and measure conventions matter; the existing measure-preserving group can contain orientation-reversing maps |
| All fixed-mass densities form the measured orbit | needs a transitivity theorem and geometric hypotheses; existing owner proves only its actual orbit |
| No mass scaling belongs to a smooth orbit | existing rigidity requires a nonzero finite measure; Lebesgue volume on `Space = ℝ³` is infinite |
| Forward-flow pushforward differentiates to `[Y,X]` | under Mathlib's bracket convention the sign is negative; pullback gives the positive bracket |
| Lie-bracket generation proves Chow–Rashevskii or an obstruction-tower equivalence | separate geometric theorem and compatibility maps are not supplied; retain as open debt |
| Constant-scale exact sequence | a separate normalizer/character construction with uniqueness hypotheses; not inferred from the general cocycle |

## Dependency order

1. Native conjugation action and group-action Galois closure.
2. Actual Fréchet pushforward action on the existing smooth group.
3. Time-zero generator equivariance and stabilizer/centralizer transport.
4. Algebraic generation plus invariant-measure closure inclusion.
5. Instantiate on the already-defined Arnold flow and restrict its symmetry
   group to the existing measure stabilizer; build its native orbit quotient.

These are theorem dependencies. Similar terminology in the contact,
coadjoint, Fisher, and Lie-bracket owners does not add an edge.

The concrete family `smoothFlowHom (σ i)` consists of mutually commuting
horizontal translations depending on the unchanged third coordinate. It
instantiates the general group-action theorems but does not witness
noncommuting bracket generation. The ambient action theorems retain the
arbitrary noncommutative group and the correct multiplication order.

## Implemented owner interfaces

| New owner | Named theorems | Main interface |
| --- | ---: | --- |
| [`Erlangen/FlowSymmetryClosure.lean`](../lean/InfoGeometry/Erlangen/FlowSymmetryClosure.lean) | 14 | `conjugateFlow`, `flow_stabilizer_eq_centralizer`, `fixingSubgroup_flowFamily_eq_centralizer_generatedSubgroup`, `invariantClosure`, `invariantClosure_generatedSubgroup_le_stabilizer_iff` |
| [`Canonical/SmoothVectorFieldPushforward.lean`](../lean/InfoGeometry/Canonical/SmoothVectorFieldPushforward.lean) | 15 | `pushforward`, `contDiff_pushforward`, `pushforward_mul`, `vectorField_stabilizer_pushforward`, `fixingSubgroup_le_span_stabilizer`, `hasDerivAt_conjugateFlow`, `flow_stabilizer_le_vectorField_stabilizer`, `vectorFieldOrbitEquivQuotient` |
| [`Canonical/ArnoldSDiffFlowErlangenClosure.lean`](../lean/InfoGeometry/Canonical/ArnoldSDiffFlowErlangenClosure.lean) | 11 | `sdiff_erlangen_closure_of_measure_invariant_flows`, `sdiff_invariantClosure`, `measureRestricted_flow_stabilizer_map`, `arnold_flow_pushforward_velocity`, `arnold_timeMaps_commute`, `arnold_family_erlangen_closure`, `arnoldVolumeFlowOrbitEquivQuotient` |

The theorem counts refer to explicit source declarations. They are distinct
from the all-declaration audit inventory, which also includes definitions,
instances and generated/private declarations.

For a flow `Φ : T →* G`, the centralizer is that of `Set.range Φ`, not of one
chosen time map. For a family `F`, it is the centralizer of the entire
algebraically generated subgroup. Restricting coordinate changes to the
measure stabilizer maps the restricted flow stabilizer to the intersection
of that centralizer and SDiff in the ambient smooth group.

To use the vector-field action, open the scoped namespace
`InfoGeometry.Canonical.SmoothVectorFieldPushforward`. Its explicit `SMul`,
`MulAction` and `DistribMulAction` instances share the same Fréchet
pushforward by construction. The flow action is separately scoped under
`InfoGeometry.Erlangen.FlowSymmetryClosure`. The span theorem additionally
uses the native `Pointwise` scope for submodule transport.

## Acceptance plan and role separation

- Root and an isolated candidate author construct the new mathematical code.
- A separate semantic reviewer checks theorem strength, hypotheses, action
  conventions, examples, scope, and reuse without authoring the audited code.
- Independent QA rebuilds the selected source closure and enumerates all
  declarations owned by the new modules, including generated declarations.
- Owner warnings are treated as errors. No proof holes, `native_decide`,
  custom axioms, partial/unsafe proofs, or vacuous witness fields are accepted.
- Actual permitted transitive axioms are limited to `propext`,
  `Classical.choice`, and `Quot.sound` and are reported from the audit.
- Native compilations and cache hydration use the repository shared lock;
  dependency pins and existing caches are preserved.
- Static refutation, semantic-vacuity, source-scope, and staged proof checks
  are reported separately from compilation. Root and umbrella validation is
  not inferred from a selected closure check.

## Verified mathematical scope

**[kernel_verified] [accepted_limited_scope]** Independent QA accepted the
mathematical source at local snapshot
`8bc9b736251e8c6d05d4171aae43095a10fc9c4d` on 2026-11-28. This acceptance covers
the three new owners, their exact selected 36-module repository import
closure, and all declarations owned by those three modules. It does not
certify the normal publication hook, any umbrella module, or the whole
repository. Final documentation changes preserve the accepted mathematical
and verifier bytes.

The complete selected closure consists of 33 unchanged baseline dependencies
and three new owners. The independent fresh run compiled the 33 dependencies
and the first two owners, then failed in the final owner. The successful
continuation verified and reused exactly those 35 artifacts, compiled the
repaired final owner, and ran the complete three-owner declaration audit.
This is **a fresh 35-module prefix plus a verified one-module delta**, not a
second fresh 36-module rebuild and not a relabeling of the earlier failed run.

All three new mathematical owners passed with `-DwarningAsError=true` and
zero compiler diagnostics. The repaired final owner exited 0 in 497.212
seconds. The complete declaration audit also ran with warnings treated as
errors and exited 0 in 1332.947 seconds. Both final commands and the integrity
checks ran under one exclusive lease of `/tmp/info-geometry-build.lock`.

### Declaration and axiom inventory

| Owner | Explicit named theorems | All theorem-kind records | Definition records | All declarations |
| --- | ---: | ---: | ---: | ---: |
| `Erlangen.FlowSymmetryClosure` | 14 | 19 | 4 | 23 |
| `Canonical.SmoothVectorFieldPushforward` | 15 | 18 | 5 | 23 |
| `Canonical.ArnoldSDiffFlowErlangenClosure` | 11 | 15 | 2 | 17 |
| **Total** | **40** | **52** | **11** | **63** |

The 52 theorem-kind records include the 40 explicitly named source theorems,
generated helpers, and one proposition-valued scoped instance. The audit
inventory is therefore distinct from the explicit theorem count. Every
source theorem was found in the audit; generated/private declarations are
included according to their actual module ownership.

The actual transitive axiom union is exactly:

```text
Classical.choice
Quot.sound
propext
```

Every audit record was independently inspected. Unsafe declarations: 0;
partial declarations: 0; owned/custom axioms: 0; unexpected transitive axioms:
0. These proofs use the stated foundational axioms and are not described as
axiom-free.

### Accepted source and environment correspondence

Independent preflight, postflight, and acceptance inspection checked all 36
source files against their frozen snapshots and committed blobs; all 33
baseline dependencies against `e2aa23c`; and all 35 reused artifacts against
the preserved successful outputs. The four maintained verifier files,
compiler binary/version, Mathlib revision, and all eight Mathlib dependency
revisions were also checked. The Mathlib and dependency tracked worktrees
were clean. Dependency pins and mathematical baseline sources remain
unchanged; existing caches were preserved, and no acceptance rule was
weakened.

| Mathematical owner | Source SHA-256 |
| --- | --- |
| `InfoGeometry.Erlangen.FlowSymmetryClosure` | `33c8b1cb4680b6d1a106d622946cb0014ccd47673b8445dd27cce55005ca82c2` |
| `InfoGeometry.Canonical.SmoothVectorFieldPushforward` | `01700ec46e49cba1341dd14c6c62496e6a927e34b1456d9c96370292b563da2f` |
| `InfoGeometry.Canonical.ArnoldSDiffFlowErlangenClosure` | `aa904d78e8ee598ffb6ef06313659d0f322d3c4d3a54940f38cc36e8f9d84c44` |

Lean is `v4.34.1`, compiler commit
`5045d0056413266e57c625dcd7c365b10e377c52`; the invoked compiler binary has
SHA-256 `e8baaa71855a616dc351028f3ad2200051b0671f423a1696a100e809302d5550`.
Mathlib is `d13f23b723b8a846827a245b89c10fc7d3f11612`.

| Mathlib dependency | Verified revision |
| --- | --- |
| `Cli` | `e92c9f15fdfacc8536f31cfb3b7ad26c3c8cd204` |
| `LeanSearchClient` | `ddf04cf3949fa556442341e87d47f9f6e6074707` |
| `Qq` | `6a489d9af5d0c47e5b259e2e8bcdfc1811b5a259` |
| `aesop` | `355695d523e41d0554926416cba2a2b3544fbbc9` |
| `batteries` | `f2effa3d803fda822b1f97b806c47cf2adfbcbc2` |
| `importGraph` | `e928b72544873815af278d38681b31c0293588e3` |
| `plausible` | `118aa17ee84656b8bd727fef7c458ee8c833385c` |
| `proofwidgets` | `106ff4fafc74ef4ac99d81dbf3ab399118f497a5` |

### Exact native invocations

The original fresh selected-source invocation below ran at snapshot
`e214e98fac206c745544bae62d953b833f93f75c`. It exited 1 after the 35 successful
modules and the first final-owner elaboration failure. Its artifacts, source
manifest, logs and failure disposition remain preserved.

```bash
python3 tools/quality/check_operator_geometry.py \
  --repo /workspace/scratch/f884dd457982/arnold-upstream \
  --mathlib /workspace/scratch/882633407e39/flow-runtime/mathlib \
  --lean /workspace/scratch/f884dd457982/arnold-runtime/lean-4.34.1-linux/bin/lean \
  --work-dir /workspace/scratch/f884dd457982/arnold-upstream-independent-qa \
  --owner InfoGeometry.Erlangen.FlowSymmetryClosure \
  --owner InfoGeometry.Canonical.SmoothVectorFieldPushforward \
  --owner InfoGeometry.Canonical.ArnoldSDiffFlowErlangenClosure \
  --base-ref e2aa23c786c63c8992e8936346ed5f7782e4e164 \
  --owner-warnings-as-errors \
  --audit \
  --audit-source /workspace/scratch/f884dd457982/arnold-upstream/tools/quality/ArnoldSDiffErlangenDeclarationAudit.lean
```

The final provenance-bound delta invocation exited 0. Its independent
inspection issued `ACCEPTED_WITH_LIMITED_SCOPE`. This separate runner leaves
the maintained checker unchanged, validates the exact reused outputs, calls
the unchanged audit validator, and records the complete native argument
arrays and `LEAN_PATH` in `commands.json`.

```bash
/opt/codex/runtimes/codex-primary-runtime/dependencies/python/bin/python3 /tmp/arnold-upstream-independent-delta-runner-2-f884dd457982.py \
  --repo /workspace/scratch/f884dd457982/arnold-upstream \
  --previous-work /workspace/scratch/f884dd457982/arnold-upstream-independent-qa \
  --failure-record /workspace/scratch/f884dd457982/arnold-upstream-independent-qa-failure-record.json \
  --mathlib /workspace/scratch/882633407e39/flow-runtime/mathlib \
  --lean /workspace/scratch/f884dd457982/arnold-runtime/lean-4.34.1-linux/bin/lean \
  --work-dir /tmp/arnold-upstream-independent-delta-qa-2-f884dd457982 \
  --expected-head 8bc9b736251e8c6d05d4171aae43095a10fc9c4d \
  --expected-runner-sha256 f7e09ed18271b6c32b98287d8ee749a05ec826d09e2706d27d57c81dac6fe290
```

The runner SHA-256 is
`f7e09ed18271b6c32b98287d8ee749a05ec826d09e2706d27d57c81dac6fe290`.
A fresh reproduction on the accepted source can use the maintained selected-
source checker above with a new work directory. The accepted continuation
itself is recorded as reuse plus delta, not as that fresh reproduction.

### Preserved verification receipts

The successful delta receipts are under
`/tmp/arnold-upstream-independent-delta-qa-2-f884dd457982`.
Earlier failed runs are separate and unchanged.

| Receipt | SHA-256 |
| --- | --- |
| `source-manifest.json` | `251833372a3a5f137a3f103650f58a60fce5cadb63d4abdd52c2462a0a5b524e` |
| `checked-hashes.json` | `aa27bc657008efff3d53c62f8ba7abbe74c4722d9e88add380b5da1409cd7545` |
| `commands.json` | `b69e853617ad6a670db6ed2e401778ea2cd126a6c83d46969951a59fc3435885` |
| `declaration-audit.jsonl` | `4b76ce3de061e976551e7781e046a81cc0a1a24a62fe974cdf877762e4f9f5f5` |
| `postflight-integrity.json` | `be62eb609c55c67a331348e6f46ed65546c6ac74098838b9d952b5eb9a5f2fcd` |
| `result.json` | `f801612e8955de37f7f066f46d6a956eb9235e0483afdf9bf06f6700dbf536ab` |
| `qa-acceptance.json` | `d60e48c405936bb643c86222b4a179567b77d72c7fd8bb8ea7f78be67105da7f` |
| Original fresh-run failure/provenance record | `4eb6899e511c62336ff8fc40884ded545e97e95ef2ce507c9089a1587e82c256` |
| First repaired-owner delta failure review | `326579028465fe2445d8f72816eb72fd859bee54b1970272386a8d5714d91228` |
| Final-source static checks | `b6de69946d84bcfd460ce71de7337edd13cbea6e79216ffe6613ada91780c806` |

The original final-owner failure was the explicit-argument use of
`Subgroup.closure_le.mpr`. A first repair exposed a centralizer rewrite
through coerced set membership. The accepted proof instead uses the
already-proved `generatedSubgroup_le_iff`, preserving every statement,
hypothesis, import, and the ordered commutation argument. The two failed runs
remain failures; neither produced the successful audit.

Earlier candidate runs also exposed a competing function-action instance and
an explicit time-zero argument in the smooth owner. The accepted source
links scoped `SMul`, `MulAction`, and `DistribMulAction` instances to the same
Fréchet pushforward. Independent semantic review accepted all repairs and
all three owners at their final hashes.

## Static analysis and warning scope

The final-source static record is bound to snapshot `8bc9b736` and the three
accepted owner hashes. The following commands exited 0:

```bash
python3 tools/quality/placeholder_audit.py --strict --json-out /workspace/scratch/f884dd457982/arnold-upstream-static-final-candidate/placeholder-report.json lean/InfoGeometry/Erlangen/FlowSymmetryClosure.lean lean/InfoGeometry/Canonical/SmoothVectorFieldPushforward.lean lean/InfoGeometry/Canonical/ArnoldSDiffFlowErlangenClosure.lean
python3 tools/quality/semantic_vacuity_gate.py --fail-on error --json-out /workspace/scratch/f884dd457982/arnold-upstream-static-final-candidate/vacuity-configured-report.json lean/InfoGeometry/Erlangen/FlowSymmetryClosure.lean lean/InfoGeometry/Canonical/SmoothVectorFieldPushforward.lean lean/InfoGeometry/Canonical/ArnoldSDiffFlowErlangenClosure.lean
python3 tools/quality/repo_lean_scope_audit.py --fail-on authoritative lean/InfoGeometry/Erlangen/FlowSymmetryClosure.lean lean/InfoGeometry/Canonical/SmoothVectorFieldPushforward.lean lean/InfoGeometry/Canonical/ArnoldSDiffFlowErlangenClosure.lean tools/quality/ArnoldSDiffErlangenDeclarationAudit.lean
```

The strict placeholder scan found zero findings. The source-scope audit
covered the three owners plus the declaration-audit source, with zero debt.
The configured semantic-vacuity gate found zero errors and five warning-level
`trivial_surface` equations: `conjugateFlow_apply`, `smul_flow_apply`,
`invariantClosure_apply`, `smul_field_apply`, and
`conjugateFlow_apply_point`. Independent review accepted them as meaningful
definitional/action-interface equations. Their `rfl` proofs are retained.

The actual staged proof gate passed while committing the accepted Lean
sources. Its scope is distinct from native compilation and from the push
gate. The 33 unchanged baseline dependencies produced 36 compiler warnings:

| Unchanged baseline owner | Warnings |
| --- | ---: |
| `Quantum.MobiusRealCotangentLift` | 4 |
| `Volume.Base` | 1 |
| `Stratum.Gauge` | 1 |
| `Projective.ExpectationRatioMetric` | 16 |
| `Projective.LogRatioDifferential` | 9 |
| `Architecture.MatrixSymmetricConeFisherRao` | 5 |

The remaining baseline owners had no compiler diagnostics. This is not a
warning-free claim for the whole selected closure; the three new owners and
the final audit were checked with warnings treated as errors.

## Publication gate and integration debt

**The normal pre-push gate has not passed. No branch or PR for this change
has been published.** The mathematical acceptance above does not substitute
for that separate repository requirement.

| Hook attempt | Source snapshot | Observed disposition |
| --- | --- | --- |
| Earlier root-build attempt | `e214e98fac206c745544bae62d953b833f93f75c` | Root Lake exited 1 because `external_refs/Stacks` was absent. Static axiom/debt and semantic-content scans passed. The task-owned hook was subsequently interrupted at the standalone-audit stage with termination code 130; no complete gate result. |
| Latest normal-gate attempt | `194b3ad7881162b6e646112b30056cd5bf1fec6d` | Root dependency compilation began. The output-capture wrapper raised `OSError: [Errno 28] No space left on device` and exited 1. A failed `Mathlib.Tactic.Linter.FlexibleLinter` build was the last captured stage; its full diagnostic and the root Lake/hook exit codes were not captured. No complete gate result. |

These attempts preceded the final centralizer proof repair. The final
accepted source has no successful normal-hook disposition. The hook's
new-ref banner says full root gate, but the observed post-build invocation
selected the three changed owners and standalone audit; no whole-repository
coverage is inferred from the banner.

The exact recorded Stacks, HomotopyHypothesis and Atlas source/configuration
checkouts were restored locally before the latest attempt without changing
tracked pins. Their package/toolchain compatibility was not established by
that restoration. The separate fetch of the recorded GIFT revision failed
with `not our ref`; that fetch failure is not substituted for the actual
ENOSPC/capture outcome of the latest root gate.

Existing caches and all prior verification evidence were preserved. Redundant
task-owned source candidates were losslessly relocated and an older clean
checkout was narrowed by reversible sparse checkout to recover workspace
capacity. No running Lake process was killed. No root retry was presented as
successful, and no cache deletion, dependency symlink, pin change, or local
Lake package override was used to bypass the remaining root-environment
problem.

The maintained checkout-consolidation helper requires preserving existing
checkouts and creating no symlinks. Native Lake path overrides would change
effective dependency resolution, and the current root inventory does not
validate those overrides. The supported isolated path-sharing workflow has
selected-source scope and cannot certify the normal root publication gate.

The latest normal-gate receipt is
`/workspace/scratch/f884dd457982/arnold-upstream-publication-gate-attempt3/receipt.json`,
SHA-256 `f0e8513dd7683dcbd0f275f407e049fa11a8b13a91a3a72bc4e282b1e90b3c1c`.
The root policy in `AGENTS.md` and `docs/HIVE_AGENT_COMMANDMENTS.md` forbids
bypassing that gate without an applicable user exception. The previous
reductive-shear draft exception was for a different change. This bridge is
prepared for review; no merge readiness or publication is claimed.

The verifier changes remain narrow: the selected-source checker restores the
missing continuation of its baseline `subprocess.check_output` call and uses
selected `owners` rather than global `OWNERS`. The new audit basename is
added to both current standalone-audit routing expressions, preserving all
existing GRH, GRR, Wilson and other routes. No umbrella module is changed.
