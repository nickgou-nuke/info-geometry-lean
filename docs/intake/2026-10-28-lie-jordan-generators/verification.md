# Verification record: real Lie–Jordan generators and matrix geometry

## Accepted source and scope

`[kernel_verified]` and `[accepted_limited_scope]` for all twenty target
modules in PR #253 and their exact twenty-nine-module repository import closure.

The [dedicated run](https://github.com/nickgou-nuke/info-geometry-lean/actions/runs/40724385803)
passed on 2026-10-28. Its
[primary job](https://github.com/nickgou-nuke/info-geometry-lean/actions/runs/40724385803/job/122943577810)
and [artifact](https://github.com/nickgou-nuke/info-geometry-lean/actions/runs/40724385803/artifacts/12832775979)
record exact-source compilation, exhaustive native declaration ownership and
axiom inspection, and a successful isolated native Lake build.

- Accepted proof-source commit: `0d01c812d7f6ca735bdff85ba3ae432d8533cdc5`.
- Base commit: `cb7482d86eadb42f2ab9c2f6f624d67b7bfe7ce4`.
- Compiled PR merge: `bb088ecfe4d0ce9ca4e9743a01f3275f94cfc5cc`.
- Identical source and merge tree: `8a25cc9da8109fe4bf7d8f16c4bfc8b3fc2feae6`.
- Artifact: 83,207 bytes, 65 entries.
- Artifact SHA-256: `91c7ff93ad6422b8ddb23af5df978f7af5a7c62477171bf0b7be7c85d85d6774`.
- Lean: `4.34.1`, compiler commit `5045d0056413266e57c625dcd7c365b10e377c52`.
- Lake: `5.0.0-src+5045d00`.
- Mathlib: `d13f23b723b8a846827a245b89c10fc7d3f11612`.

[verification-status.json](verification-status.json) is the unchanged successful
`status.json` from that artifact. Its SHA-256 is
`9e8af32065c3df5e946593bd7cf4aa50289622408dbd702b99ff3cd48547ea05`.
It records the exact repository import DAG, all twenty-nine source hashes,
compiler versions, a clean source checkout, empty constructivity findings,
native declaration counts, and the successful Lake result.

The archive digest agrees with GitHub's artifact metadata and upload log.
Every copied source agrees byte-for-byte with the working source and its
accepted Git blob. Primary GitHub commit records independently establish the
identical source and merge trees. This evidence-only follow-up changes no Lean
source, verification control, dependency pin, or root package metadata.

## Public theorems and native declarations

The two latest streams contribute **117 new public theorem declarations**.
Together with the previous accepted development, PR #253 contains **413 public
theorem declarations across twenty target modules**.

| Owner | Added public theorems | Added audited native declarations |
| --- | ---: | ---: |
| Existing `Core.LieJordanBoundaryOperators` | 3 | 6 |
| `Core.PeirceSandwichDuality` | 14 | 23 |
| `Core.LieJordanGenerators` | 33 | 48 |
| `Canonical.LieJordanGeneratorTrace` | 15 | 21 |
| `Canonical.RealLieJordanGeometry` | 17 | 26 |
| `Canonical.RealLieJordanExamples` | 35 | 54 |
| **Extension** | **117** | **178** |

The twenty targets own **615 native declarations**. The entire repository
closure owns **886 unique native declarations**. Native counts include
definitions, private helpers and compiler-generated proof declarations; they
are not public theorem counts.

The five new target owners account for 172 native declarations. The existing
boundary owner increases from 31 to 37: precisely the three added public
theorems and their three generated `_abel_1_1` proof declarations. No prior
native name is removed. The three newly reached existing dependency owners
contribute another 25 declarations.

Twenty of the twenty-one sources in the
[previous accepted closure](../2026-10-28-lie-jordan-boundaries/verification.md)
retain their hashes and complete native name sets. The only modified previous
owner is `Core.LieJordanBoundaryOperators`, with the three contracted additions.

## Compiler, axiom and native build evidence

All twenty-nine source modules compiled with zero Lean warnings. Every direct
compiler log is empty. All twenty target modules were compiled with
`-DwarningAsError=true`. No warning setting or acceptance criterion was
disabled. The staged proof-integrity gate and exact-source constructivity scan
passed.

The complete native audit reports:

```text
AUDIT_AXIOMS: [propext, Classical.choice, Quot.sound]
AUDIT_COUNT: 886
```

Native module ownership selects every declaration in the repository closure,
including private and generated declarations. The audit rejects unsafe and
partial declarations and every axiom outside the three listed foundational
axioms. Its enumeration contains 886 distinct names; all owner counts and
completion markers agree with the successful status record. Every one of the
413 public source theorem names appears under its expected native module
owner, including declarations carrying inline attributes.

The generated audit source agrees exactly with the unchanged audit generator.
There are no accepted `sorry`, `admit`, custom axioms, unsafe declarations or
partial declarations.

The isolated native Lake package registers all twenty-nine repository modules
as roots. Its log explicitly records all twenty-nine as built and ends with:

```text
Build completed successfully (3414 jobs).
```

The job count includes dependency work. The verifier checked the pinned
dependency revisions and clean dependency sources before compilation and again
after the native build, then rechecked original and copied source hashes.
The pinned Mathlib manifest was also independently read during acceptance.

## Verification controls

The verifier has SHA-256
`7872a388a385136c9d6af1fe40927e0772973f388307d86d458a6b666c2cd7ea`.
The dedicated workflow has SHA-256
`404aca89952578e8847bb50b5ad8b3aaa305db25603c0c35dcc066c10bbc5d1b`.

Relative to the previous accepted head
`adc916d7a8e9370401251901156ae8551ed01d39`, only five target entries were
appended to the verifier and eight source paths were appended to the workflow.
All twenty-nine repository closure paths are covered by workflow triggers.
The closure has 41 direct native Mathlib imports.

The closure walker, audit generator, constructivity scanner, build lock,
acceptance logic, root Lake configuration, manifest and toolchain are unchanged.
No verification threshold was relaxed to admit this extension.

## Independent semantic and artifact acceptance

The independent semantic reviewer read the frozen streams, native repository
and Mathlib owners, the theorem implementations, contract and prerequisite
map. Its final reconciliation accepted source `0d01c812` and the exact hashes
of all six touched Lean owners plus the contract and mathematical map, with no
unresolved semantic blocker.

That review confirmed the two distinct skew generators and their signs,
ordinary versus weighted trace laws, explicit cancellation of four, exact
stationarity/idempotence criteria, real transpose adjunction, the common
centralizer and orthogonal range, and the dense noncommuting witnesses.
The affine curve uses native matrix product topology and compatible
`Matrix.Norms.Elementwise` calculus instances. The Frobenius geometry retains
its separate explicit native matrix inner-product structure. The direct
`Mathlib.Algebra.Order.Star.Real` import supplies the proved real ordered-star
instance without adding a theorem hypothesis.

A separate independent artifact reviewer inspected the primary job and commit
records, all 65 archive entries, all source copies and compiler logs, the
complete native declaration enumeration, generated audit source, native Lake
log, dependency pins and verification controls. It returned
`[accepted_limited_scope]` for the exact source and compiled merge above.
It reconciled all 886 unique native declarations and all 413 public theorem
names, the three-axiom footprint, all twenty-nine explicit Lake builds, the
source/merge trees and the artifact digest.

The parent independently repeated the artifact-to-source, compiler-log,
native-owner/count/axiom, audit-source and native-Lake reconciliation.
The semantic and artifact reviewers did not author the accepted theorem
content or modify verification controls. Generation, semantic review and
artifact acceptance remained separate roles.

## Mathematical acceptance boundary

The [contract](contract.md) and [mathematical map](mathematical-map.md) preserve
input order, identify canonical owners and record the proof-prerequisite
partial order. Edges denote mathematical prerequisites.

The accepted extension uses native associative algebra endomorphisms and full
real matrix algebras. It includes reflection/sandwich intertwiners and native
kernel/range identities, all three generator expansions, distinct ordinary
and reflection-weighted trace laws, real stationarity criteria, and exact
bridges to the existing Heisenberg-oriented jump term.

The real Frobenius results prove the actual transpose adjunction, the negative
sum-of-squared-commutators energy identity, native self-adjointness and operator
positivity of the negative paired generator, the common-centralizer kernel,
and its orthogonal range. They consume the existing real adjoint-pair energy
and common-kernel theorems after establishing adjunction; no square-zero
assumption on the ordinary commutator action is made.

Preservation of matrix positive semidefiniteness by the paired sandwich is a
separate theorem from positivity of an endomorphism's Frobenius quadratic form.
The dense real examples are `[countermodel_found]` with full Lean proofs:
they refute unconditional idempotence and skew-plus stationarity of the
proposed complement, the conflated unit/trace laws, and unconditional
positivity of the skew sandwich.

The curve theorem proves the initial condition and native `HasDerivAt`
operator equation, together with an exact negative quadratic form for every
positive time. It does not assert an exponential identification or uniqueness.
Ordinary transpose, reflection-metric transpose, weighted trace and positive
Frobenius inner product remain distinct.

No complete-positivity classification, general semigroup theorem, cohomology
calculation, continuum limit or physical interpretation is inferred from these
results. Such stronger claims remain outside this accepted scope.

## Reproduction

With the repository-pinned Lean available and a clean Mathlib checkout at the
recorded revision, run from the repository root:

```sh
python3 tools/quality/check_lie_jordan_geometry.py \
  --mathlib-root /absolute/path/to/pinned-mathlib \
  --output /absolute/path/to/fresh-verification
```

The checker takes the shared build lock, rejects another active compiler,
fetches the native import cache, compiles exact source copies, audits native
declaration ownership and builds an isolated native Lake package. Existing
manifests and dependency sources are preserved. This checks the recorded
closure; it is not an exhaustive build of the repository's root aggregators.

## General repository workflows

The seven general workflow failures were inspected in their primary logs at
immediate parent `0cd077446097712879397dcc87023b957c5e847f`. The sole subsequent
proof-source change is the direct native real ordered-star import. All
affected workflow, configuration, script, dependency and filename paths are
unchanged at the accepted source and agree with both base `cb7482d8` and
previous accepted head `adc916d7`.

| General workflow | Observed failure | Primary evidence |
| --- | --- | --- |
| General CI | Missing/untracked Atlas and uninitialized GIFT; the later compiler-bridge smoke also lacks Atlas | [job](https://github.com/nickgou-nuke/info-geometry-lean/actions/runs/40723681172/job/122941161410) |
| Lean style | Existing `PellisFineStructure.lean` / `PellisfineStructure.lean` case collision | [job](https://github.com/nickgou-nuke/info-geometry-lean/actions/runs/40723681246/job/122941104825) |
| Docs | GitHub Pages site lookup returns Not Found | [job](https://github.com/nickgou-nuke/info-geometry-lean/actions/runs/40723681322/job/122941105539) |
| Sorry Gate | Missing `lake` executable, exit 127 | [job](https://github.com/nickgou-nuke/info-geometry-lean/actions/runs/40723681215/job/122941104376) |
| Reviewed integration | Machine-local `pure_math_lib` clone URL is unavailable | [job](https://github.com/nickgou-nuke/info-geometry-lean/actions/runs/40723681198/job/122941104717) |
| Closure Debt | Python cannot import `pytest` | [job](https://github.com/nickgou-nuke/info-geometry-lean/actions/runs/40723681293/job/122941104274) |
| Post-build quality | Missing `external_refs/atlas-lean` | [job](https://github.com/nickgou-nuke/info-geometry-lean/actions/runs/40723681294/job/122941105082) |

These reproduce the previously inspected failure categories. The independent
reviewer and parent both read these primary logs. No failure in this table is
reported in a new theorem owner. The successful dedicated proof verification
does not imply repository-wide CI success.
