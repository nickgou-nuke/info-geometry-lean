# Verification record

## Verified source and scope

`[kernel_verified]` and `[accepted_limited_scope]` for the five new modules and their exact ten-module
repository import closure. The dedicated
[verification run](https://github.com/nickgou-nuke/info-geometry-lean/actions/runs/40672796153)
passed on 2026-10-28. Its
[job log](https://github.com/nickgou-nuke/info-geometry-lean/actions/runs/40672796153/job/122763556505)
and [raw artifact](https://github.com/nickgou-nuke/info-geometry-lean/actions/runs/40672796153/artifacts/12808668306)
contain the direct compiler, axiom-audit and native Lake evidence.

- Source commit: `f76d541643569af9b706bfcfcc991d4edb034cd4`.
- Base commit: `cb7482d86eadb42f2ab9c2f6f624d67b7bfe7ce4`.
- Compiled PR merge: `b174e8f0123819cb568aea179272996f69472222`.
- Artifact SHA-256: `cfd29a90b9c9efbdb577dabf47e6edbd63d069092f281e6e5349d7a5b3c3d8c1`.
- Lean: `4.34.1`, compiler commit `5045d0056413266e57c625dcd7c365b10e377c52`.
- Lake: `5.0.0-src+5045d00`.
- Mathlib: `d13f23b723b8a846827a245b89c10fc7d3f11612`.

[verification-status.json](verification-status.json) is the unchanged successful
`status.json` from that artifact. It records every module's SHA-256, the exact
import DAG, declaration counts, compiler versions, clean source checkout, empty
constructivity findings, and successful isolated Lake build. These source
fingerprints also match the committed Lean files. This documentation-only record
does not change any verified source, verifier, workflow, or dependency pin.

## Results

| New module | Source theorem declarations | Audited native declarations |
| --- | ---: | ---: |
| `Core.LieJordanComposition` | 17 | 31 |
| `Core.OperatorCliffordDouble` | 40 | 82 |
| `Core.PeirceStarCharges` | 18 | 26 |
| `Canonical.LieJordanMatrixGeometry` | 18 | 28 |
| `Canonical.LieJordanMatrixExamples` | 21 | 33 |
| **Total additions** | **114** | **200** |

All ten repository modules compiled with zero warnings. The five new modules
were checked with `-DwarningAsError=true`. The native declaration audit covered
**442 declarations** across the full closure, including generated and private
declarations; its per-owner enumeration and counts were reconciled.

The complete axiom set was:

```text
AUDIT_AXIOMS: [propext, Classical.choice, Quot.sound]
AUDIT_COUNT: 442
```

The audit rejects unsafe or partial declarations and any other axiom, including
admitted proofs. The constructivity scan found no placeholders, custom axioms,
or vacuous proof substitutes. The staged proof-integrity gate passed.

The isolated native Lake package registered all ten source owners and rebuilt
all ten repository modules. Its log ends with
`Build completed successfully (3114 jobs).` The job count also includes native
dependency work; it is not a count of newly proved theorems. Before and after
verification, the checker verified pinned dependency revisions and clean
dependency worktrees, and checked that both original and copied sources retained
their recorded hashes.

The verifier source has SHA-256
`973ed875624611a9f062836b933110e1d6bbfc19a24b39a8b659271cbacebaf4`;
the dedicated workflow has SHA-256
`469191e397b526e3e5326fa9fd5e55c659ca7b1af3290ccc85ffebb60ca580aa`.

## Independent semantic review

An independent review context reread both streams, the existing owners, native
Mathlib APIs, and all five new modules. It returned `[audit_pass]` on the exact
Lean source bytes recorded here. It confirmed both ordered-product signs,
injective-doubling hypotheses, full four-block coverage, faithful operator
lifting, the distinct trace pairings, the negative Gram identity, Peirce star
conditions and nilpotent expression, and the noncommuting matrix witnesses.
It found no blocking semantic issue or weakening of the contracted conclusions.

A second independent review context inspected the successful raw artifact,
all ten compiler logs, copied sources, frozen Git blobs, native declaration
enumeration, generated audit source, dependency/version records, and Lake log.
It returned `[accepted_limited_scope]` for source commit `f76d5416`. It also
confirmed that the compiled merge and accepted head have the identical Git tree
`0f542bed62913211d68d084ec9fa9ae85b7d52f4`. Neither review context authored the
accepted theorem content; semantic review and compiler evidence were assessed
separately. Acceptance is limited to the exact source and build scope above.

The mathematical scope is associative algebra, module endomorphisms, full finite
complex matrices, algebraic idempotent tangency, trace pairings, star projections,
and positive semidefinite Gram squares. Self-adjointness and injectivity of
doubling are explicit `[bucket_2_conditional]` hypotheses where required.
The wrong unrestricted product sign and the identification of the two trace
quadratic expressions have explicit `[countermodel_found]` witnesses.

State-dependent BKM metrics, manifold connections or curvature, unbounded
operator domains, PDE and continuum interpretations remain `[bucket_3_open_debt]`.
No positive-definiteness theorem, positivity preservation of the normalized
trace-zero vector field, or universal Clifford-algebra representation theorem
is asserted.

## Reproduction

With the repository-pinned Lean available and a clean Mathlib checkout at the
revision above, run from the repository root:

```sh
python3 tools/quality/check_lie_jordan_geometry.py \
  --mathlib-root /absolute/path/to/pinned-mathlib \
  --output /absolute/path/to/fresh-verification
```

The checker takes the shared build lock, checks for another active compiler,
fetches the exact native import cache, compiles fresh source copies, audits native
declaration ownership, and builds a separate Lake package. It preserves existing
manifests and dependency sources and uses native caches without deleting or
symlinking them. The successful scoped check does
not establish a build of the repository's exhaustive root package.

## Existing general CI failures

General workflow failures were independently compared with the unchanged base.
The root workflow/configuration blobs and affected dependency paths were checked
against the base; the matching raw failures precede or prevent their intended
acceptance checks. No general-CI success is claimed.

| General check | Matching failure | PR evidence | Base evidence |
| --- | --- | --- | --- |
| CI | Missing Atlas checkout; uninitialized GIFT gitlink | [run](https://github.com/nickgou-nuke/info-geometry-lean/actions/runs/40672312916) | [run](https://github.com/nickgou-nuke/info-geometry-lean/actions/runs/40646581439) |
| Sorry Gate | `lake` executable absent, exit 127 | [run](https://github.com/nickgou-nuke/info-geometry-lean/actions/runs/40672313202) | [run](https://github.com/nickgou-nuke/info-geometry-lean/actions/runs/40664918012) |
| Closure Debt | Python `pytest` unavailable | [run](https://github.com/nickgou-nuke/info-geometry-lean/actions/runs/40672312930) | [run](https://github.com/nickgou-nuke/info-geometry-lean/actions/runs/40657982601) |
| Docs | GitHub Pages configuration returns 404 | [run](https://github.com/nickgou-nuke/info-geometry-lean/actions/runs/40672312941) | [run](https://github.com/nickgou-nuke/info-geometry-lean/actions/runs/40646582103) |
| Lean style | Existing `KRDualityCascade.lean` / `KrDualityCascade.lean` case collision | [run](https://github.com/nickgou-nuke/info-geometry-lean/actions/runs/40672312652) | [run](https://github.com/nickgou-nuke/info-geometry-lean/actions/runs/40646581399) |
| Reviewed integration | Machine-local `/home/goutev/repos/pure_math_lib` clone URL unavailable | [run](https://github.com/nickgou-nuke/info-geometry-lean/actions/runs/40672312928) | [run](https://github.com/nickgou-nuke/info-geometry-lean/actions/runs/40646581397) |
| Post-build quality | Missing `external_refs/atlas-lean` | [run](https://github.com/nickgou-nuke/info-geometry-lean/actions/runs/40671102089) | [run](https://github.com/nickgou-nuke/info-geometry-lean/actions/runs/40646581360) |

The first six PR comparisons are recorded at `c620a1d0`; the post-build comparison
is at `ca51fc25`. Those existing workflows, root package/dependency configuration,
and case-colliding files remain unchanged in this PR. Later source refinements
were confined to the five new modules and their dedicated verifier. These
baseline failures are separate from the successful scoped run cited above.
