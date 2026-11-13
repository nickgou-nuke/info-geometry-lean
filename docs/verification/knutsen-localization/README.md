# Knutsen localization verification record

## Scope and source

This package records the formalization of projection localization, isometric
range corners, finite operator frames and Weyl masks, the real porosity-loss
recurrence, metric-hole preservation under thickening, and conditional
multiscale estimates. The mathematical contract is
[KNUTSEN_LOCALIZATION_CONTRACT.md](../../KNUTSEN_LOCALIZATION_CONTRACT.md).

The original intake is preserved verbatim in [intake.txt](intake.txt), with
SHA256 `bd31543386a90075f8bea22af36bdc630983313f5148eb6e2de6f2bfdfdb7db0`.
The implementation was reviewed in an independent checkout against upstream
base `a392af178af1fe2bcba2ba39eb405700c6ee103c`. The earlier active candidate
checkout was left untouched.

Lean remains `leanprover/lean4:v4.34.1`; Mathlib remains
`d13f23b723b8a846827a245b89c10fc7d3f11612`. No dependency revision, toolchain,
axiom whitelist, or repository gate was weakened for this change.

## Mathematical owners

| Owner under `lean/InfoGeometry/` | Proved content |
| --- | --- |
| `OperatorAlgebra/ProjectionLocalization.lean` | Complementary Gram conservation, leakage and commutator variance, native star-order inequalities, and C-star norm/commutation criteria. |
| `OperatorAlgebra/IsometryCornerLocalization.lean` | An explicit non-unital star-ring embedding, an equivalence with the native range corner, complement and power transport, norm preservation, and the projection-preservation criterion. |
| `OperatorAlgebra/FiniteOperatorFrame.lean` | Rectangular synthesis/Gram identities, operator-valued multiplier laws, an existing Kraus-sum bridge, and Parseval Gram projections over arbitrary noncommutative star rings. |
| `Clifford/WeylFrameMasks.lean` | Native unitaries from the Jones generators, actual windowed masks, the unnormalized twirl law, and an equal-cardinality counterexample. |
| `Analysis/PorosityIteration.lean` | The real recurrence, finite-sum and closed forms, monotone loss, uniform half bound, and retained-fraction estimates. |
| `Analysis/MetricPorosity.lean` | Genuine disjoint metric holes, their shrinkage under open thickening, and the single-thickening recurrence bridge. |
| `Analysis/MultiscaleLocalization.lean` | Conditional one-step energy iteration, terminal-energy bounds, and norm estimates for ordered noncommutative products. |

Both production umbrellas import mathematical owners. Native declaration
enumeration is a separate verification command, not an umbrella dependency.

## Acceptance status

Fresh native verification passed in
[CI run 43383097703](https://github.com/nickgou-nuke/info-geometry-lean/actions/runs/43383097703/job/131745210917)
on published source head `3f7282ceb5076e16bae8acc696adffd3771494c9`.
The runner checked pull-request merge revision
`8e9221d29001ebe80558237992ce9be8a35920af`; all sixteen source hashes and
all four verifier-source hashes match the reviewed local checkout at
`0149b1f0a017b423d318b54e84662a7e6dd32022`.

| Check | Actual result |
| --- | --- |
| Fresh source-closure compilation | All sixteen modules exited zero; no project elaboration was reused. |
| Compiler warnings in the seven new owners | Zero. |
| Native declaration audit | Passed for 490 declarations, including private and generated declarations; 154 belong to the seven new owners. |
| Transitive axiom set | Exactly `propext`, `Classical.choice`, and `Quot.sound`. |
| CI placeholder audit with `--strict` | Passed: zero hard findings; eight soft findings retained for review. |
| CI semantic audit with `--fail-on error` | Passed: zero errors; thirteen heuristic warnings retained for review. |
| Independent strict local placeholder scans | Seven commands exited zero; zero hard findings and eight soft findings. |
| Independent semantic warning-threshold scan | Exited one for thirteen `trivial_surface` warnings; zero semantic errors and complete input coverage. |
| Independent findings review | All twenty-one static findings individually reviewed; zero unresolved findings. Two existing dependency compiler lints retained. |

The downloaded [artifact 14017786847](https://github.com/nickgou-nuke/info-geometry-lean/actions/runs/43383097703/artifacts/14017786847)
matches GitHub's ZIP SHA256
`848fa6c5663cf19fbc48a5570ac3bf40ce0d1441f49ab5bdfd5162fc667b91d3`.
Its internal evidence manifest, generated audit source, source fingerprints,
compiler version, dependency pin, positive per-owner declaration counts, and
axiom log were reconciled independently.

The [independent acceptance receipt](independent/acceptance.json) binds the
native evidence and actual local strict-scan receipts to the reviewed source.
The [individual dispositions](independent/findings-dispositions.json) explain
the short defining equations, algebraic simplifications, and finite-cardinality
lemmas identified by the heuristics. The semantic warning-threshold exit code
remains one in the preserved record; acceptance includes the independent
mathematical review of those warnings.

The exact selected repository source closure has sixteen modules: seven new
mathematical owners and nine reused owners. The maintained checker verifies
source and verifier hashes, the pinned compiler and Mathlib revision, and
transitive repository dependency fingerprints. Its native audit examines all
explicitly selected owners, including private and generated declarations, and
allows only `propext`, `Classical.choice`, and `Quot.sound`.

The final native evidence comes from fresh CI compilation and audit. Queued
local incremental acceptance attempts were cancelled while still waiting for
the shared build lock; no repaired local acceptance run is claimed. The first
local development pass and the successful isolated Weyl candidate check retain
their distinct scopes. Native acceptance uses the independently reconciled
fresh CI evidence rather than repeating the same checked source. It does not
certify every tracked file or the whole root Lake package.

## Observed repair history

1. The first development pass exposed a missing pinned `Idempotents.olean`,
   unfinished Weyl-twirl simplification, two Multiscale API/notation issues,
   and a deprecated Real import. That pass omitted the native axiom audit and
   is retained as failed development evidence.
2. The missing artifact was restored under the shared build lock from a clean
   Mathlib checkout at the identical revision, after matching the source file.
   The source/API repairs preserved the theorem statements. The isolated Weyl
   candidate compiled with exit code zero and no warnings.
3. The initial dedicated CI run failed during project checkout on an existing
   gitlink without a `.gitmodules` URL. The scoped workflow now removes the
   checkout credential directly before executing repository code. The repaired
   checkout and credential removal succeeded in the next run.
4. CI run `43382041378`, at head
   `475acd7b1bb32e1943b597892e56bebf6ee05f8f`, freshly compiled all sixteen
   modules successfully. All seven new owners had zero compiler warnings.
   The strict native audit then rejected the generated executable helper
   `remainingPorosity._unsafe_rec`, so that run is not an axiom certificate.
5. The reviewed repair marks only the recurrence definition explicitly
   `noncomputable`. It keeps the safe kernel definition, recurrence equations,
   theorem statements, hypotheses, and proof bodies. The explicit modifier
   prevents generation of the executable helper; the surrounding
   `noncomputable section` did not do so. No audit exception is introduced.

The two compiler warnings in reused owners concern an unnecessary tactic
sequence in `Core.PeirceDecomposition` and an unused simp argument in
`Clifford.OperatorValuedJones`. They are preserved as existing warnings.

## Publication gates and interpretation

The actual staged proof gate passed for the source checkpoint, workflow repair,
and explicit-noncomputability repair. The actual root pre-push gate exited one
at the earlier source checkpoint `26c53a3a7ae6d9a12b4b83604767c801791dc99c`.
It invoked a locked `lake build` including both changed umbrellas and all seven
new owners, but Lake failed during package setup because
`external_refs/homotopy-hypothesis-lean4` was absent. Its subsequent source-debt,
semantic-content, tracked-scope, and quarantine scans passed. The pre-push hook
did not reach its later full-root stage, and no final-head root-build or
pre-push certificate is asserted. The dependency configuration was unchanged
by the subsequent one-keyword proof-surface repair.

Exact hook invocation:

```text
.githooks/pre-push origin https://github.com/nickgou-nuke/info-geometry-lean.git
```

Its standard input selected local source checkpoint `26c53a3a` on
`refs/heads/codex/knutsen-localization` as a new remote ref. The full captured
output and return code are retained in `hooks/`.

The broader CI failures were reconfirmed on the same published source head.
[The baseline job](https://github.com/nickgou-nuke/info-geometry-lean/actions/runs/43383097585/job/131745247308)
reports missing/untracked `HomotopyHypothesis` and `Atlas` path packages and an
uninitialized `GIFT` gitlink; its later Lake attempt fails on the missing
`HomotopyHypothesis` directory.
[The style job](https://github.com/nickgou-nuke/info-geometry-lean/actions/runs/43383097857/job/131745210694)
reports the existing `PellisFineStructure.lean` / `PellisfineStructure.lean`
case collision. Those failures concern unchanged repository surfaces; their
exact-head excerpts and provenance are retained under `ci/current-code-head/`.
The PR remains a draft while these root publication blockers are unresolved.

The formalization retains arbitrary noncommutative coefficients. Positivity
and faithful vanishing require their stated native order or C-star hypotheses.
A finite mask is not identified with Euclidean porosity. The one-step energy
and operator norm bounds remain explicit assumptions.

The full analytic fractal uncertainty principle remains outside this proof
scope: the Gaussian STFT/Bargmann construction, Fock subaveraging and sampling,
the geometric-to-energy implication, and lattice condition (H) are not proved
by these finite algebraic identities and recurrence bounds. Knutsen's Lemma
5.2 is a Fock sampling/norm formula, not the finite Gram-square identity.

## Reproduction

See [the exact target list and commands](../../../verification/knutsen-localization/README.md).
The final package includes native and static reports, complete command
receipts, reviewed findings, source and evidence hashes, and the generated
native audit source. Build binaries are deliberately excluded.
