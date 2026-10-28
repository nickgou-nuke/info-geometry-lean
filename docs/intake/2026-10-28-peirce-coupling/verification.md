# Verification record: opposite Peirce coupling

## Verified source and scope

`[kernel_verified]` and `[accepted_limited_scope]` for the nine new targets and
their exact fifteen-module repository import closure.

The [dedicated verification run](https://github.com/nickgou-nuke/info-geometry-lean/actions/runs/40680219671)
passed on 2026-10-28. Its
[job log](https://github.com/nickgou-nuke/info-geometry-lean/actions/runs/40680219671/job/122788752150)
and [raw artifact](https://github.com/nickgou-nuke/info-geometry-lean/actions/runs/40680219671/artifacts/12811754016)
record exact-source compilation, a complete native ownership/axiom audit, and a
successful isolated native Lake build.

- Source commit: `a628db82d4ef8780d1df156ccd57f62f743472c8`.
- Base commit: `cb7482d86eadb42f2ab9c2f6f624d67b7bfe7ce4`.
- Compiled PR merge: `961bd066139532ebd5e0aa7fe7e3782ff4671b20`.
- Identical source and merge Git tree: `8097193e0766ee1f48b48a017a6f94ced2d499b0`.
- Artifact SHA-256: `0081459f0ca00c785d770fdf56475347ef2a7e9c656f5673b9819e4d2e35f8d1`.
- Lean: `4.34.1`, compiler commit `5045d0056413266e57c625dcd7c365b10e377c52`.
- Lake: `5.0.0-src+5045d00`.
- Mathlib: `d13f23b723b8a846827a245b89c10fc7d3f11612`.

[verification-status.json](verification-status.json) is the unchanged successful
`status.json` from the artifact. Its SHA-256 is
`120027a402a58aaaf0b2761fbc8149e2fb29b5dcfcb9955727989572e2f2b2a7`.
It records all fifteen source hashes, the exact repository import DAG, native
declaration counts, compiler versions, clean source checkout, empty
constructivity findings, and the successful Lake build. The copied source bytes
match the source commit and current Lean files. This evidence-only addition
changes no proved source, verification control, or dependency pin.

The new four-module extension adds **83 source theorem declarations**. Together
with the earlier five modules, PR #253 adds **197 source theorem declarations**
in nine modules. The current run checks all nine targets and their complete
**fifteen-module repository import closure**. It includes the earlier layer
again; the ten source hashes recorded in the
[previous verification record](../2026-10-28-lie-jordan-peirce/verification.md)
remain unchanged.

## Results

| New module | Source theorem declarations | Audited native declarations |
| --- | ---: | ---: |
| `Core.LieJordanComposition` | 17 | 31 |
| `Core.OperatorCliffordDouble` | 40 | 82 |
| `Core.PeirceStarCharges` | 18 | 26 |
| `Canonical.LieJordanMatrixGeometry` | 18 | 28 |
| `Canonical.LieJordanMatrixExamples` | 21 | 33 |
| `Core.PeirceCoupledCorners` | 31 | 34 |
| `Canonical.PeirceCouplingGeometry` | 14 | 17 |
| `Canonical.PeirceCouplingPositivity` | 18 | 20 |
| `Canonical.PeirceCouplingExamples` | 20 | 30 |
| **All additions** | **197** | **301** |

All fifteen repository modules compiled with zero warnings; each direct compiler
log is empty. The nine new targets were checked with
`-DwarningAsError=true`. The complete closure audit enumerated **547 native
declarations**, including generated and private declarations. The four new
coupling modules own 101 of those declarations; the existing
`Core.PeirceMatrixTracePairing` contributes four additional declarations beyond
the earlier ten-module closure.

The complete axiom set was:

```text
AUDIT_AXIOMS: [propext, Classical.choice, Quot.sound]
AUDIT_COUNT: 547
```

The audit rejects unsafe or partial declarations and every other axiom,
including admitted proofs. Native module ownership and the per-owner counts
were reconciled with the declaration enumeration. The constructivity scan
reported no findings, and the staged proof-integrity gate passed.

The isolated native Lake package registered all fifteen source owners and
rebuilt all fifteen repository modules. Its log ends with:

```text
Build completed successfully (3302 jobs).
```

The job count includes dependency work; it is not a theorem count. The verifier
checked dependency revisions and clean dependency worktrees before the isolated
Lake build and again at completion, and rechecked both original and copied
source hashes.

The expanded verifier has SHA-256
`048790fbf8976758cb0887328943213344621e50a735f4c42115cb074eb4c36f`;
the dedicated workflow has SHA-256
`c624d9eef7d97d740cd6fed8b9582201a84c1303694adf837d69ef3ab52bc0c9`.
Relative to the previously accepted verifier, only the four targets were
appended. The workflow's path coverage was expanded for those targets and the
existing trace-pairing owner. No acceptance logic was weakened.

## Independent reviews

An independent semantic reviewer reread both supplied streams, existing owners,
native Mathlib APIs, and all four final coupling modules. It returned
`[audit_pass]` for the exact hashes in the status record. The final changes
removed unused instance assumptions and normalized conjugated numerals; no
mathematical conclusion was replaced or weakened.

The semantic review confirmed the reflection/compression signs, characteristic-two
validity, existential nonzero-coupling argument without cancellation of two,
native kernel equalities, adjoint-pairing hypotheses, the exact positive-definite
criterion, and both dense noncommuting matrix witnesses.

A second independent reviewer inspected the successful raw artifact, all fifteen
compiler logs, copied and committed sources, generated audit source, complete
native declaration enumeration, dependency/version records, and Lake log. It
returned `[accepted_limited_scope]` for source commit `a628db82`, reconciled all
547 unique native declarations, and confirmed identical head/merge trees. It
also checked that the earlier ten-module source hashes and owner counts were
unchanged. Neither independent review context authored the accepted theorem
content. Semantic review and compiler acceptance were assessed separately.
Acceptance is confined to the exact mathematical and build scope recorded here.

## Mathematical acceptance boundary

The new extension proves the contracted arbitrary-ring support, square,
compression, reflection, parity, and zero identities. Its matrix layer proves
native trace balances, existence of a detecting opposite partner, and exact
kernel submodule equalities. With a star projection and adjoint pairing, it
proves the Gram-square identity, positive semidefiniteness, exact zero/trace
detection, and positive definiteness precisely when the two corner kernels
intersect trivially.

The input classification is now resolved within that finite mathematical scope:
the independent-corner statements are `[kernel_verified]`; adjoint-paired
positive conclusions retain their explicit `[bucket_2_conditional]` hypotheses;
the two boundary examples are `[countermodel_found]` with complete Lean proofs.
The examples refute unrestricted positivity for independent opposite inputs and
positive definiteness inferred solely from nonzero coupling. The factors
`U,Uᴴ` and `U,-Uᴴ` do not commute. Their two opposite products do commute by
support; this does not restrict the factors or the full matrix carrier.

The singular positive example concerns the whole space. It does not refute a
positive bound after restriction to the kernel complement. No information metric,
differential connection, curvature, topological invariant, particle interpretation,
symmetry-breaking theorem, unbounded-operator theorem, or continuum spectral gap
is asserted by this extension. Those interpretations remain
`[bucket_3_open_debt]`.

## Reproduction

With the repository-pinned Lean available and a clean Mathlib checkout at the
revision above, run from the repository root:

```sh
python3 tools/quality/check_lie_jordan_geometry.py \
  --mathlib-root /absolute/path/to/pinned-mathlib \
  --output /absolute/path/to/fresh-verification
```

The checker takes the shared build lock, checks for another active compiler,
fetches the exact native import cache, compiles fresh source copies, audits
native declaration ownership, and builds a separate Lake package. It preserves
existing manifests and dependency sources, without deleting or symlinking
existing caches. This establishes the stated source closure and isolated
native package; it does not establish an exhaustive root-package build.

## General repository checks

At source head `f6c8ad15544889536238d7b882cb52456cbc470e`, six completed general
workflows failed on existing infrastructure or repository conditions. Five
reproduced the recorded baseline failure signatures. The style checker reported
another pre-existing case collision, with both files unchanged from the base.

| General check | Observed failure | Current evidence |
| --- | --- | --- |
| Sorry Gate | Missing `lake` executable, exit 127 | [job](https://github.com/nickgou-nuke/info-geometry-lean/actions/runs/40679766622/job/122787187698) |
| Closure Debt | Python `pytest` unavailable | [job](https://github.com/nickgou-nuke/info-geometry-lean/actions/runs/40679766634/job/122787188458) |
| Docs | GitHub Pages configuration returns 404 | [job](https://github.com/nickgou-nuke/info-geometry-lean/actions/runs/40679766756/job/122787188974) |
| Lean style | Existing `PellisFineStructure.lean` / `PellisfineStructure.lean` case collision | [job](https://github.com/nickgou-nuke/info-geometry-lean/actions/runs/40679766654/job/122787188075) |
| Reviewed integration | Machine-local `pure_math_lib` clone URL unavailable | [job](https://github.com/nickgou-nuke/info-geometry-lean/actions/runs/40679766608/job/122787188133) |
| Post-build quality | Missing `external_refs/atlas-lean` | [job](https://github.com/nickgou-nuke/info-geometry-lean/actions/runs/40679766635/job/122787187948) |

The [previous verification record](../2026-10-28-lie-jordan-peirce/verification.md)
links the baseline logs. Independent review compared all seven general workflow
blobs, root package/dependency configuration, and affected dependency paths
against the base; they are unchanged. Both currently reported case-colliding
files are also unchanged. The next source commit `a628db82` changed only
numeral normalization in the example trace proof.

The separate [general CI run](https://github.com/nickgou-nuke/info-geometry-lean/actions/runs/40679766597)
was still installing Lean at the 11:28:41 UTC audit cutoff; no failure or success
was inferred for that run. No repository-wide CI success is claimed. These
general checks are separate from the successful scoped verification above.
