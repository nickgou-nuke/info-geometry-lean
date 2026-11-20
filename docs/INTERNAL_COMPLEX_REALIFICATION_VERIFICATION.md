# Internal complex realification: verification and scope

## Publication source and integration status

The seven new owners have **independent mathematical and native compiler
acceptance at the finite scope below**. Root Lake integration and the installed
pre-push gate returned exit 1 at the missing `HomotopyHypothesis` path package.
The source is presented as a draft for review, with those failures disclosed.
The [theorem contract](INTERNAL_COMPLEX_REALIFICATION_CONTRACT.md) defines the
actual carriers, conventions, constructions, and remaining implications.

The change is stacked on upstream PR #413, branch
`codex/divergence-modular-closure-20261119`, base commit
`4d7b8d4b2e22768abe6d9b13990c2da9fe495ffb`, base tree
`794a5724bf9712791038d11818f67105f0f6a22e`.
The installed pre-commit hook accepted implementation commit
`e78781478dd501d11ca74a8a12fd2c33351eb60f`, tree
`68ac65afcdde749ceac5c31157950953c671374c`.
This verification document is a later documentation-only addition. The seven
accepted owners, contract, workflow, `All.lean` wiring, verification helpers,
and pins remain unchanged. The accompanying PR records the final published
tree and commit; upstream CI is reported only against an observed source head.

The next sections reproduce the independent QA findings. The reviewer's
recorded base HEAD predates the implementation commit; acceptance identifies
the exact source bytes, not an assertion that new files were in the base commit.

## Verdict and source identity

**ACCEPTED_WITH_LIMITED_SCOPE.** The seven selected owners passed fresh native
compilation and complete owned-declaration axiom auditing. Independent A-A
semantic review and declaration-specific heuristic adjudication found no
remaining mathematical blocker within the stated finite-dimensional contract.

This reviewer did not author proofs, edit repository sources, change dependency
pins, or alter any maintained verification helper. All compiler and static gate
runs were serialized under `/tmp/info-geometry-build.lock`. Candidate generation,
semantic review, and this acceptance run used separate agent contexts.

The recorded checkout head was `4d7b8d4b2e22768abe6d9b13990c2da9fe495ffb`. The new implementation was
staged and uncommitted over that base when QA began. The accepted identity is the
exact source snapshot and SHA-256 record, not a claim that these edits were
already contained in the base commit. Working files, staged blobs, fresh compiler
snapshots, and all ten A-A reviewed file hashes reconciled with **zero mismatches**.

## Fresh native compiler and axiom audit

```bash
python3 tools/quality/check_clifford_dirac.py \
  --mathlib-root /workspace/scratch/0b027a897d29/lean_verification_runtime/mathlib4 \
  --lean /workspace/scratch/0b027a897d29/lean_verification_runtime/lean-4.34.1/bin/lean \
  --output /workspace/scratch/0b027a897d29/hestenes-verification/qa-final/kernel \
  --target InfoGeometry.Quantum.RealificationPhaseGrading \
  --target InfoGeometry.Quantum.RealificationKrein \
  --target InfoGeometry.Quantum.RealificationCFC \
  --target InfoGeometry.Canonical.MatrixRealificationThermodynamics \
  --target InfoGeometry.Clifford.EvenInternalComplex \
  --target InfoGeometry.Clifford.Cl55InternalComplex \
  --target InfoGeometry.Quantum.CliffordPhaseRealification
```

The command exited **0**. It used neither `--incremental` nor `--skip-audit`.
All **42 repository modules** in the dynamically resolved import closure compiled
freshly; no repository artifact was reused. All **seven selected owners had zero
compiler warnings**. The **36 warnings in unchanged prerequisite owners** are
retained in the native report and are not relabeled as a warning-free whole
repository result.

| Selected owner | All owned declarations audited |
| --- | ---: |
| `Quantum.RealificationPhaseGrading` | 40 |
| `Quantum.RealificationKrein` | 11 |
| `Quantum.RealificationCFC` | 27 |
| `Canonical.MatrixRealificationThermodynamics` | 28 |
| `Clifford.EvenInternalComplex` | 50 |
| `Clifford.Cl55InternalComplex` | 17 |
| `Quantum.CliffordPhaseRealification` | 31 |
| Total | **204** |

The count includes private and generated declarations. It is not a claim of 204
new substantive theorem statements. The maintained native audit recursively
inspected each declaration's dependency axioms and found only `propext`,
`Classical.choice`, and `Quot.sound`. It rejected neither an unsafe/partial
reviewed declaration nor an additional axiom, because none was found.

The actual fingerprint was:

- `Lean (version 4.34.1, x86_64-unknown-linux-gnu, commit 5045d0056413266e57c625dcd7c365b10e377c52, Release)`
- `Lake version 5.0.0-src+5045d00 (Lean version 4.34.1)`
- Mathlib `d13f23b723b8a846827a245b89c10fc7d3f11612`
- Toolchain `leanprover/lean4:v4.34.1`

Pins, Mathlib sources, and maintained kernel-checker helpers remained unchanged.

## Static acceptance and retained heuristic findings

| Check | Observed result |
| --- | --- |
| Strict OpenGauss source screen | Exit 0, no traps |
| Strict OpenGauss refutation | Exit 0, seven PASS reports |
| Gate 4 source preflight | Exit 0, all seven `STATIC_REVIEW_PASSED_KERNEL_UNVERIFIED` |
| Exact-file style API | Seven files read, zero findings |
| Exact-file lexical axiom/debt API | Seven files read, zero gaps or read failures |
| Strict placeholder audit | All seven exits 0; zero hard and zero advisory findings; seven SOFT findings |
| Warning-strict semantic-vacuity gate | **Exit 1**, thirteen `trivial_surface` warnings |
| Staged and working whitespace | Both exits 0 |
| Workflow and registration validation | Passed at the scope described below |

Gate 4 here is explicitly a static preflight. Its own JSON correctly says that
it did not run kernel verification; the separate fresh native compiler/audit
above supplies that evidence. Gate 4 ran from 10:16:42.715027 UTC to
10:22:35.015918 UTC, about 5 minutes 52 seconds, including its repeated staged
proof gate checks. The run was not interrupted or substituted.

The style CLI traverses directories and would not reliably cover a single-file
argument, so QA invoked its maintained `audit_file` API on the exact seven files
and recorded coverage. Likewise, QA used the maintained lexical `scan_files`
API to avoid that CLI's fixed repository report output. These are exact
source checks; neither is presented as a compiler certificate.

The raw semantic-vacuity exit **remains 1**. Its thirteen warnings identify short
representation/API lemmas such as the internal axis, zero rotor, coercion
readouts, scalar/charge linearity, and ordered-word transport. The seven SOFT
placeholder findings identify five short bridge lemmas and two generic data
parameters `Q : QuadraticForm ℝ M`. They do not identify seven proof holes.

Independent A-A review inspected all **17 distinct flagged surfaces** and their
constructions or consumers. Its declaration-specific adjudication found them
legitimate and required no source repair. It did not relabel the raw warning
command as passed or hide the automated SOFT labels. See
the declaration-specific adjudication below for every disposition.

## Workflow, source coverage, and registration

The scoped workflow YAML parsed successfully. Its **four Bash bodies** passed
`bash -n`, and its **three embedded Python blocks** parsed with Python's AST
parser. Its exact seven-target list matched QA. Every one of the **42 repository
source-closure paths**, plus the required verifier/pin/contract/registration
paths, is covered by a pull-request trigger.

The three terminal imports in `InfoGeometry.All` reach all seven selected
owners. This is import registration validation; QA did not compile the whole
`InfoGeometry.All` aggregate. The workflow's fresh-output, exact-head, explicit
zero-selected-warning, and native axiom requirements were inspected separately
from any later observed upstream CI run.

## Accepted mathematics and boundaries

Acceptance covers the actual real internal phase plane, faithful realification
of homogeneous components, native even-Clifford right phase, explicit
matrix/Clifford phase intertwiner, real matrix functional calculus, normalized
Gibbs/relative-entropy transport, generalized charge balance, and distinct
Krein/grading conventions described in the theorem contract.

The logarithm and square-root theorems retain positive Hilbert-order hypotheses;
Krein-selfadjointness is not substituted for them. The source/reference matrices
and generalized Hermitian charges are not assumed to commute. Relative modular
operators intertwine on the encoded image rather than identifying differently
sized full Hilbert–Schmidt carriers.

This does not establish the full matrix operator algebra and its positive CFC
inside the entire `Cl(5,5)` even carrier, a full fine Lie grading classification,
the paper's signed modular-index carry construction, a complete Dirac
representation, infinite-dimensional modular standard form, or a physical heat
engine/gauge model.

Root Lake integration and installed publication gates are a separate parent
workstream. This QA verdict does not claim they passed, and it does not clear
previously observed external path-dependency blockers. A later upstream CI result
must identify the published head independently.


## Declaration-specific semantic adjudication

The following independent A-A dispositions retain all automated warnings and
SOFT labels. They do not replace or relabel any raw scanner exit status.

### The 13 `trivial_surface` warnings

Names in this table identify the declaration in the named source owner. Several lexical `decl_ref` values use a module prefix; the actual Lean namespace for the `Realification*` matrix owners is `InfoGeometry.Quantum.Realification`.

| Owner and declaration | What the short proof actually establishes | Substantive consumer or API role; disposition |
| --- | --- | --- |
| `Canonical.MatrixRealificationThermodynamics.realify_chargePencil` | Realification commutes with the existing finite real charge pencil by the proved sum and real-scalar transport laws. | Explicitly used by `generalizedGibbs_state` to identify the actual real noncommuting generator inside the exponential. This is a finite-linear-map bridge, not an assumed Gibbs identity. Accepted. |
| `Clifford.Cl55InternalComplex.coe_phaseBivector55` | Coercing the concrete native even element gives the actual product `ι55 (e_pos 0) * ι55 (e_pos 1)`. | Public readout of the native embedding. The substantive construction separately proves orthogonality, `phaseBivector55_sq`, phase injectivity, and distinct reversal/parity behavior. This accessor need not itself repeat those proofs. Accepted. |
| `Clifford.Cl55InternalComplex.nativeRealK55_phase_apply` | The phase operator of the concrete `RealKVect` is exactly right multiplication by the already constructed `phaseBivector55`. | Readout of the real module action. `nativeRealK55_phase_sq`, `nativeRealK55_commutes_left`, and `matrixPhaseHom55_internalJ` operate on this actual object. The square law is supplied by a proved Clifford calculation, not an arbitrary unproved field. Accepted. |
| `Clifford.EvenInternalComplex.coe_planeBivector` | The native even embedding of a vector pair coerces to `ι Q u * ι Q v`. | Coercion API for the actual Clifford carrier. `planeBivector_sq` derives the square from native relations under orthogonality and norm-product hypotheses; `reverse_planeBivector` and the parity theorem use the same constructed element. The name alone does not assert purity for nonorthogonal vectors. Accepted. |
| `Clifford.EvenInternalComplex.leftObservable_apply` | Evaluating the bundled left observable gives `a * x`. | Readout of `leftObservable`, whose morphism compatibility is proved by the existing left/right regular associativity theorem. The statement does not assert a new commutation law by reflexivity; it exposes the map whose commutation was separately established. Accepted. |
| `Clifford.EvenInternalComplex.phasePlaneMap_apply` | Evaluating the real linear coordinate map yields `p.1 • 1 + p.2 • B`. | Explicitly used in `matrix_internal_scalar_action` and the complex exponential comparison. Native intertwining and injectivity are separately proved. The unrestricted map is not asserted injective or two-dimensional without the later square-minus-one/nontriviality hypotheses. Accepted. |
| `Clifford.EvenInternalComplex.rotorElement_zero` | The actual cosine/sine phase element at zero equals the algebra unit. | Explicitly used in both `rotorElement_mul_neg` and `rotorElement_neg_mul`, after the nontrivial native multiplication law. A correct group identity normalization has a short proof. Generic Spin membership is expressly not claimed. Accepted. |
| `Quantum.CliffordPhaseRealification.matrixPhaseHom_apply` | The composite of the actual coordinate isomorphism and native phase map reads the two matrix coordinates as `x_left • 1 + x_right • B`. | API for the constructed composite. `matrixPhaseHom_internalJ`, `matrix_internal_scalar_action`, and `matrix_internal_rotor_action` establish the substantive action intertwining; the concrete `Cl55` instance discharges the square hypothesis. This is not an assumed representation witness. Accepted. |
| `Quantum.RealificationCFC.realifyStarAlgHom_apply` | The bundled star-algebra map evaluates to the existing realification. | Essential readout API for CFC naturality: the bundled map has actual unital, multiplicative, real-linear and star-preserving proofs. `realify_cfc`, logarithm, and square-root transport use that actual map and proved continuity. The short accessor is not the functional-calculus theorem. Accepted. |
| `Quantum.RealificationPhaseGrading.internalScalar_axis` | The real coordinate coefficient `(0,1)` is the actual block matrix `internalJ`. | Public normalization for the internal scalar definition. Multiplication, complex-scalar comparison, homogeneous planes, and rotor laws are separately proved on this same definition. No larger classification or global centrality is claimed by the accessor. Accepted. |
| `Quantum.RealificationPhaseGrading.internalRotor_zero` | The actual real matrix phase at zero equals the matrix identity. | Explicitly consumed by `internalRotor_mul_neg`, `internalRotor_orthogonal`, and `internalRotor_preserves_metric`. It is a valid identity-element calculation, not placeholder debt. Accepted. |
| `Quantum.RealificationPhaseGrading.internalRotor_transpose` | The real Hilbert transpose of the cosine/sine phase equals the phase at the negative angle, using the proved `internalJ_transpose` and trigonometric parity. | Explicitly consumed by ordinary orthogonality and the commuting-metric preservation theorem. The proof is short because the native transpose and scalar APIs already supply the necessary algebra. Accepted. |
| `Quantum.RealificationPhaseGrading.realify_weylD` | The realification of the existing ordered word `X^a Z^b` equals the same ordered word of the realified generators, using multiplication and power transport. | Explicitly used throughout `realify_weylD_mul` and `realify_weylD_bracket`; these retain the ordered coefficient and sign. It does not assume a word product, discard a cocycle, reduce exponents modulo `N`, or assert fineness. Accepted. |

The table deliberately distinguishes explicit named-lemma consumers from readout APIs whose underlying constructions are consumed after definitional reduction. It does not claim every accessor is cited by name in another proof, nor does it count a definitional accessor as an independent research result.

### The seven SOFT placeholder signals

| Signal file | Exact declaration or surface | Declaration-specific adjudication |
| --- | --- | --- |
| `placeholder-0-signals.json` | `realify_weylD`, `skeletal-proof` | The complete proof expands the existing ordered word and applies proved homomorphism laws. Its substantive product and bracket consumers are identified above. Replacing `simp only` with artificial extra proof steps would add no mathematical obligation. No unproved placeholder is present. |
| `placeholder-2-signals.json` | `realify_isStrictlyPositive_iff`, `skeletal-proof` | This translates the separately proved `realify_posDef_iff` through Mathlib's native equivalence between strict positivity and positive definiteness. The preceding proof establishes reflection by quadratic forms and preservation by positivity plus invertibility. Consumers include `state_isStrictlyPositive` and `log_state`. It does not assume strict positivity of the desired target. |
| `placeholder-2-signals.json` | `realify_nonneg_iff`, `skeletal-proof` | This translates the existing proved `realify_posSemidef_iff` into the native matrix order using `Matrix.nonneg_iff_posSemidef`. It is used in `realify_sqrt` and `sqrt_state`. Reusing the canonical order equivalence is the intended bridge, not a missing proof. |
| `placeholder-3-signals.json` | `realify_chargePencil`, `skeletal-proof` | The finite sum is the actual existing `chargePencil`; realification's proved additive and real-scalar laws discharge the entire statement. `generalizedGibbs_state` consumes this equality inside the native exponential. Noncommuting charge products are never replaced by scalar products. |
| `placeholder-4-signals.json` | File-level `variable (Q : QuadraticForm ℝ M)`, `injected-hypothesis-surface` | `Q` is native mathematical **data**, not a proposition, axiom, or desired theorem witness. It determines the actual `CliffordAlgebra.even Q`. Geometric hypotheses are separately stated on actual vectors, their square law is proved, and the concrete `Q55` specialization supplies explicit vectors and discharged hypotheses. This is ordinary parametric algebra, not injected proof content. |
| `placeholder-5-signals.json` | `nativeRealK55_phase_apply`, `skeletal-proof` | This definitional action readout refers to a concrete native object built using the proved `phaseBivector55_sq`. Its phase square, commuting left actions, and matrix-phase intertwiner are separate theorems on that object. No placeholder record substitutes for the construction. |
| `placeholder-6-signals.json` | File-level `variable (Q : QuadraticForm ℝ M)`, `injected-hypothesis-surface` | Again `Q` chooses the native target algebra. The coordinate/matrix isomorphism is constructed explicitly, the target right action is constructed from actual multiplication, and the morphism is their actual composition. The later `matrixPhaseHom55` instantiates it with the concrete `Q55` and proved bivector square. No functional-calculus or global representation compatibility is postulated through this parameter. |

`placeholder-1-signals.json` contains no signal. The row counts above cover every emitted SOFT signal exactly once.


## Static command scope

With `<owners>` denoting the exact seven owner paths in the native command,
the recorded source checks were:

```text
python tools/infra/opengauss_screener.py <owners> --strict --json
python tools/infra/opengauss_cli.py refute <owners> --strict --json
python tools/infra/opengauss_cli.py review <owners> --gate GATE_4 --json
python tools/quality/placeholder_audit.py --root <each-owner> --strict --json-out <report> --signals-out <signals>
python tools/quality/semantic_vacuity_gate.py <owners> --fail-on warning --json-out <report>
git diff --cached --check
git diff --check
```

Exact arguments, timestamps, exit codes, and log hashes are retained in the
local `qa-final/static-commands.json`. The style `audit_file` and lexical
`scan_files` APIs checked each of the seven exact source files. They are source
checks, separate from the fresh compiler and recursive declaration audit.

## Root integration recheck

The parent actually retried the maintained root wrapper:

```bash
python3 tools/infra/run_locked_lean.py \
  --lake /workspace/scratch/0b027a897d29/lean_verification_runtime/lean-4.34.1/bin/lake \
  lean/InfoGeometry/Canonical/MatrixRealificationThermodynamics.lean
```

On 2026-11-20 this ran from 10:24:04.967 to 10:24:58.926 UTC and returned
**exit 1** during root package resolution, before compiling this owner:

```text
error: HomotopyHypothesis: package directory not found:
.../external_refs/homotopy-hypothesis-lean4
```

The root manifest's HomotopyHypothesis and Atlas path packages have no
reconstructible Git revision. GIFT core is a pinned submodule. No guessed
revision, replacement package, proof stub, destructive cache repair, or
weakened gate was introduced. The local archive used for the pinned Lean
runtime was checksum-verified as
`47bf4bbd78f70c2e9670598ab7124d92b6efb7330ff33e5fbb4030f6fd72e4e4`.

## Installed publication hooks

The installed pre-commit hook passed for the implementation commit above,
reporting `proof_proxy_staged_gate: ok`. The actual installed pre-push hook was
then invoked for that exact checked-out commit and a new remote branch:

```text
refs/heads/codex/internal-complex-pauli-realification-20261120 e78781478dd501d11ca74a8a12fd2c33351eb60f refs/heads/codex/internal-complex-pauli-realification-20261120 0000000000000000000000000000000000000000
```

```bash
bash .githooks/pre-push origin https://github.com/nickgou-nuke/info-geometry-lean.git
```

It ran from 10:27:36.136972 to 10:31:12.062495 UTC and returned **exit 1**.
The hook classified the ancestry range from merge base
`08c34e03f610b452e03422037949196dc7d92d6d` against `origin/main`.
Its locked Lake build selected 24 changed owners including `All` and failed at
the same missing HomotopyHypothesis path. The subsequent 24-file lexical
axiom/debt audit, 27,297-file semantic-content scan, tracked Lean scope audit,
and quarantine audit passed their respective gates. Historical quarantine
findings remain visible and are not promoted to proved source.

Because the ancestry-range gate failed, the hook did not reach its later full
root-package invocation. This is a failed publication-gate result. The
separately observed native closure check does not establish a successful root
build. This documentation-only follow-up records the failure without changing
the accepted proof, workflow, helper, or pin bytes. The user requested upstream
PR publication; the accompanying draft presents the finite result for review
with the failure disclosed and no merge performed.

## Accepted source fingerprints

These SHA-256 values identify the independently reviewed source bytes. The
later verification document is outside that earlier proof-source snapshot.

| Path | SHA-256 |
| --- | --- |
| `lean/InfoGeometry/Quantum/RealificationPhaseGrading.lean` | `2c9649c98490fcca66e54418e3aa8dde2eff9cb35d0ccd6d3a5ed1a8769ddd48` |
| `lean/InfoGeometry/Quantum/RealificationKrein.lean` | `27a7d7e903727bc77ddb1b642a8362b4b1204a018973b045fc8a19d92ce6b773` |
| `lean/InfoGeometry/Quantum/RealificationCFC.lean` | `6e631d076a5061251a2b3d6b0369f02878334bdf660a7e8fedbfe87393274ddf` |
| `lean/InfoGeometry/Canonical/MatrixRealificationThermodynamics.lean` | `021316f1b6b8b83afbf2b55bff2831857fe39ccadc80d6c1b2b8948b2a44bff1` |
| `lean/InfoGeometry/Clifford/EvenInternalComplex.lean` | `96c9930b36c4c7814773febca0ae9b02a76fcd62a43c730b1d03e6dd08d61e9e` |
| `lean/InfoGeometry/Clifford/Cl55InternalComplex.lean` | `bfb42b0326e38aa9729afb78626d2b7cc941bbaf50d1bb98de7d4a8e8300a993` |
| `lean/InfoGeometry/Quantum/CliffordPhaseRealification.lean` | `3dad97aff006ea4547f2127c5c5f5aeb2b14bf64cc0f7d83d2c4a4596e0c3bfb` |
| `docs/INTERNAL_COMPLEX_REALIFICATION_CONTRACT.md` | `ae378e8c7a475abb1d1d1be51dd9efa1beb12be9933cdb841a5b4ae4a691bd46` |
| `.github/workflows/internal-complex-realification.yml` | `32a65f68810e1d77488477e6dc83203df4d1ea5c931ee76c206e935a9cc937b2` |
| `lean/InfoGeometry/All.lean` | `d9602015a56dba357653a36efa03e94bfdaf77fe7e679874ae752e63421d2529` |

## Evidence fingerprints

Raw local logs are retained under the task's `hestenes-verification` directory;
these hashes identify the actual observations. This document records their
substantive outcomes. The scoped upstream workflow uploads its own fresh
reports, logs, provenance, and source snapshots, separate from these local logs.

| Evidence | SHA-256 |
| --- | --- |
| `aa-review.md` | `b9ba3f94b5d2cefee928918618b68785259045afecb965d5396f97e450b63834` |
| `aa-source-hashes.json` | `30b64cbb7ab6be0b99b9f02dfd295ab13f5f5b242c79b7bc57f4226bbba965c8` |
| `aa-heuristic-adjudication.md` | `89fe3e572efb7375279127e3bdd17808f4de65d3fdbed2c553c8ca18858db1bd` |
| `aa-heuristic-adjudication.json` | `ded315095032e63bfc826ce4c6917fd81763a1d08f96da161f7838d04e809ba4` |
| `qa-final/qa-report.json` | `f2266fccb784ee1e678735a521a44402b94c7c9123b131f2365b6929975f3d3e` |
| `qa-final/qa-report.md` | `faf8bcba9a87b4275a7ff2fa29550d7f297cb3803e47c45097a8cebc440bad51` |
| `qa-final/qa-evidence-sha256.json` | `98a500713fce93bc67683f9ec210f3ab55ece164ce547fbe25df59fac23816ed` |
| `qa-final/kernel/report.json` | `0605edd65dddb7d86dc300b01ffd6a47b48ca6d812f02e08d475daf2f8c7c1fb` |
| `qa-final/kernel/axioms.log` | `ad380c890989bcb47e6fd1f4470e92969c3bf8c9690eacf433be25f5e9757e3b` |
| `root-wrapper.log` | `395e291a4d1480f470bbd947f61448f4dc3e34ba7fae84226a937da4f6bd3abd` |
| `implementation-commit.log` | `439e2549d095f8c012266922224521e0ca69ddedcc2594e65932e870df7d2f80` |
| `pre-push.log` | `c582f0edb2b972e53c282071583634f21e4367945a56fc5e63e1f252172a135d` |

The maintained compiler helper has a fixed warning policy for its original
CliffordDirac prefix. QA additionally checked every one of these seven selected
owners for zero warnings; the new workflow explicitly enforces that same
requirement. The workflow's acceptance is for the resolved source closure,
not for the root Lake workspace or the full `All.lean` aggregate.
