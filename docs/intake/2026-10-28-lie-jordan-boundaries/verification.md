# Verification record: native noncommutative boundary operators

## Verified source and scope

`[kernel_verified]` and `[accepted_limited_scope]` for all fifteen new targets
in PR #253 and their exact twenty-one-module repository import closure.

The [dedicated run](https://github.com/nickgou-nuke/info-geometry-lean/actions/runs/40690909498)
passed on 2026-10-28. Its
[job log](https://github.com/nickgou-nuke/info-geometry-lean/actions/runs/40690909498/job/122825146079)
and [raw artifact](https://github.com/nickgou-nuke/info-geometry-lean/actions/runs/40690909498/artifacts/12817342240)
record exact-source compilation, complete native declaration ownership and
axiom inspection, and a successful isolated native Lake build.

- Source commit: `044eadd1ab686771f9b3df087ab8ee78e80b896e`.
- Base commit: `cb7482d86eadb42f2ab9c2f6f624d67b7bfe7ce4`.
- Compiled PR merge: `07aa0965ab7fc372832e2de0ccd59af8c934d611`.
- Identical source and merge Git tree: `0e3e6a84a4165c945ef36d5428957fa2ae7ac2f1`.
- Artifact SHA-256: `03e69a182d0d56db4ce1b98796bf6cd3edda1e814e0edf2840093fbd46b5ea38`.
- Lean: `4.34.1`, compiler commit `5045d0056413266e57c625dcd7c365b10e377c52`.
- Lake: `5.0.0-src+5045d00`.
- Mathlib: `d13f23b723b8a846827a245b89c10fc7d3f11612`.

[verification-status.json](verification-status.json) is the unchanged successful
`status.json` from the artifact. Its SHA-256 is
`8ef3209d37d9d59d9030c32eb8a562fc9bba5d3e9482f5ec84cf50cac5880a5f`.
It records all twenty-one source hashes, the exact repository import DAG,
module counts, compiler versions, clean source checkout, empty constructivity
findings and successful native Lake build. The artifact digest agrees with
GitHub's published digest. Copied source bytes agree with the source commit
and the working Lean files. This evidence-only addition changes no proved
source, verification control or dependency pin.

## Theorem and declaration counts

The six-module boundary extension contributes **99 public source theorem
declarations**, five private helper theorems, and two native constructions.
Together with the previously accepted nine modules, PR #253 contributes
**296 public source theorem declarations** in fifteen modules.

| Added module or accepted group | Public source theorems | Audited native declarations |
| --- | ---: | ---: |
| Previous nine targets | 197 | 301 |
| `Core.LieJordanBoundaryOperators` | 19 | 31 |
| `Core.PeirceAdjointCycle` | 13 | 14 |
| `Core.PeirceQuadraticFrame` | 27 | 36 |
| `Canonical.PeirceBoundaryComplex` | 15 | 30 |
| `Canonical.LieJordanSandwichGeometry` | 7 | 7 |
| `Canonical.LieJordanBoundaryExamples` | 18 | 18 |
| **All fifteen targets** | **296** | **437** |

The new six owners contribute 136 native declarations. The entire repository
import closure owns **683 unique declarations**, including generated and private
declarations. Native declaration counts are not public theorem counts.
All fifteen source hashes and native owner counts from the
[previous accepted closure](../2026-10-28-peirce-coupling/verification.md)
remain unchanged.

## Compiler, axiom and build evidence

All twenty-one repository modules compiled with zero Lean warnings; each direct
compiler log is empty. All fifteen targets were checked with
`-DwarningAsError=true`. No warning option or acceptance criterion was disabled.
The staged proof-integrity gate and the exact-source constructivity scan passed.

The complete audit reports:

```text
AUDIT_AXIOMS: [propext, Classical.choice, Quot.sound]
AUDIT_COUNT: 683
```

Native module ownership selects every declaration in the repository closure,
including private helpers and compiler-generated declarations. The generated
audit rejects unsafe or partial declarations and every axiom outside the listed
three foundational axioms. The complete declaration enumeration has 683 distinct
names, and its per-owner counts agree with all status counts and completion
markers. The generated audit source agrees with the unchanged audit generator.

The isolated native Lake package registers all twenty-one repository modules
as roots. Its log explicitly records all twenty-one as built and ends with:

```text
Build completed successfully (3351 jobs).
```

The job count includes dependency work. The verifier checked the exact dependency
revisions and clean dependency sources before the build and again at completion,
then reconciled original and copied source hashes. No dependency pin or root
package metadata was changed.

The verifier has SHA-256
`74d2a0720a902696988abb00e8c0da92ddcac6356eadad7b56218faa5e7cd4e6`;
the dedicated workflow has SHA-256
`060f86300f41750986f54f3a5960cbdd3532c6708fcde422e6eebc13a63ec969`.
Relative to the previous accepted head `935473bc`, only the six new targets
were appended to the verifier, and only their six source paths were appended
to the workflow. All twenty-one closure paths are covered. The closure walker,
audit generator, constructivity scanner, build lock and acceptance logic are
unchanged.

## Independent reviews

An independent semantic reviewer read the four frozen streams, native Mathlib
and repository owners, all six new modules, and the mathematical prerequisite
map. Its final review reconciled each source with commit `044eadd1` and accepted
the exact contracted scope, with no unresolved semantic blocker.

The review confirmed the two necessary source corrections, characteristic-two
validity, weighted bracket signs, actual Peirce membership, derived square-zero
law, native cochain constructor, exact trace normalization, sufficient adjoint
pairing for positivity, and all dense counterexample values. The final compiler
repairs made hypotheses explicit, normalized natural-number coefficients and
removed one unused simplifier argument; no contracted conclusion was weakened.

A separate independent acceptance reviewer inspected the primary GitHub job,
artifact and commit records, all 49 archive files, all twenty-one compiler logs,
copied/live/committed sources, generated audit source, complete declaration
enumeration and native Lake log. It returned `[accepted_limited_scope]` for
source `044eadd1`, with no acceptance blocker.

That review reconciled all 683 unique native declarations, confirmed that every
one of the 296 public source theorem declarations appears in the enumeration,
verified the three-axiom footprint and all twenty-one explicit native Lake
builds, and confirmed unchanged prior hashes/counts and verification controls.
It independently confirmed the identical source/merge trees and artifact digest.
Neither independent review context authored the accepted theorem content or
changed verification controls. Generation, semantic audit and artifact acceptance
were separate roles.

## Mathematical acceptance boundary

The [mathematical map](mathematical-map.md) records source order, canonical
operations and the proof-prerequisite partial order. The formal results use
arbitrary associative unital rings, native endomorphisms and submodules, full
finite matrices, and a native module-category cochain complex.

The exact Lie–Jordan compositions, adjoint polynomial, Peirce range/kernel
identities, weighted corner algebra, reciprocal-cycle identities, graded
differential and sandwich trace laws are `[kernel_verified]` with their stated
hypotheses. Positive preservation under adjoint pairing retains its explicit
`[bucket_2_conditional]` hypotheses; the trace-preservation equivalence states
the exact normalization condition.

The dense matrix witnesses are `[countermodel_found]` with complete Lean proofs.
They refute ordinary Lie/Jordan square-zero actions inferred from a square-zero
generator, the omitted mixed-composition defect, ambient centrality, unnormalized
tripotency and unconditional sandwich positivity for independent opposite
inputs. The ordinary-square witnesses even use an input in the actual odd
Peirce range. On the same full matrix algebra the graded differential is proved
both nonzero and square-zero.

The constant-module cochain complex is genuinely constructed from its proved
composition-zero law. No cohomology computation, adjoint-codifferential
identification, positive Hodge-Laplacian conclusion, complete-positivity theorem,
normalized inverse conclusion, curvature or continuum interpretation is
inferred; those additional claims remain `[bucket_3_open_debt]`.

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
manifests and dependency sources are preserved. The result establishes the
recorded source closure and isolated native package, not an exhaustive build
of the repository's root aggregators.

## General repository workflows

The seven general workflows at source commit `044eadd1` fail at reproduced
infrastructure or repository conditions. Their actual current logs were read;
none of the reported failure points is in a new module of this extension.

| General workflow | Observed failure | Current evidence |
| --- | --- | --- |
| Closure Debt | Python cannot import `pytest` | [job](https://github.com/nickgou-nuke/info-geometry-lean/actions/runs/40690909495/job/122825144987) |
| Lean style | Existing `PellisFineStructure.lean` / `PellisfineStructure.lean` case collision | [job](https://github.com/nickgou-nuke/info-geometry-lean/actions/runs/40690909418/job/122825144583) |
| Docs | GitHub Pages site configuration returns Not Found | [job](https://github.com/nickgou-nuke/info-geometry-lean/actions/runs/40690909586/job/122825145670) |
| Sorry Gate | Missing `lake` executable, exit 127 | [job](https://github.com/nickgou-nuke/info-geometry-lean/actions/runs/40690909423/job/122825144453) |
| Reviewed integration | Machine-local `pure_math_lib` clone URL is unavailable | [job](https://github.com/nickgou-nuke/info-geometry-lean/actions/runs/40690909596/job/122825145693) |
| Post-build quality | Missing `external_refs/atlas-lean` | [job](https://github.com/nickgou-nuke/info-geometry-lean/actions/runs/40690909567/job/122825145765) |
| General CI | Bootstrap rejects missing/untracked Atlas and uninitialized GIFT; later smoke also lacks Atlas | [job](https://github.com/nickgou-nuke/info-geometry-lean/actions/runs/40690909458/job/122825202340) |

The first six reproduce the signatures in the
[prior coupling verification](../2026-10-28-peirce-coupling/verification.md),
which links the original baseline evidence. The general CI failure was also
compared directly with the previous accepted head's
[job 122792432946](https://github.com/nickgou-nuke/info-geometry-lean/actions/runs/40681302516/job/122792432946):
the Atlas/GIFT error categories and GIFT pin agree.

Independent comparison against base `cb7482d8` confirms that all seven general
workflow configurations, root Lake configuration and pins, `.gitmodules`,
bootstrap and locked-build tools, affected dependency entries, and both
case-colliding files are unchanged. GIFT remains pinned to
`e6f3c3ac2140c2324fb2ae029c32233e73aa5e92`; Atlas has no tracked entry at either
revision. The successful dedicated verification above does not imply
repository-wide CI success.
