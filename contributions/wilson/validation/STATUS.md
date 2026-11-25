# Wilson contribution verification and publication status

The original preparation was made on 2026-11-24 against upstream commit
`9a4492cc6bdf3338379123a085af59dfd8018a9c` of
[`MathePhysics/4D_Wilson_Loop_RG`](https://github.com/MathePhysics/4D_Wilson_Loop_RG).

## Current exact destination results — 2026-11-25

The preparation now targets upstream `c25e77e9654a54fc5e4a04bfb637b7144defacc0`.
The Gaussian package and all destination toolchain/Mathlib pins are unchanged
from the original base. Packaging reads the current CoreLean umbrella before
appending contribution imports, preserving upstream's new imports.

The Gaussian extension adds native Markov kernels, exact native kernel
composition and KL data processing, plus a finite reflected-covariance
transport theorem and its adapter to the actual Schur covariance. Its
counterexample distinguishes ordinary positivity and reflection commutation
from positivity on the selected time half.

All four jobs in [run 45571203500](https://github.com/nickgou-nuke/info-geometry-lean/actions/runs/45571203500)
passed at preparation source `ff8e1632b45569d88da1c73c0ec160c913fe55f9`:

| Contribution | Destination Lean | Public theorems | Fresh reports | Result |
| --- | --- | ---: | ---: | --- |
| Weighted Gaussian algebra, native Markov kernels and reflected covariance | 4.34.0-rc2 | 78 | 80 | PASS |
| Cutoff comparison and real power-log summability | 4.36.0 | 16 | 16 | PASS |
| Complex finite Gram quotients and Hilbert colimit | 4.36.0 | 27 | 29 | PASS |
| Positive compatible limits from summable state errors | 4.36.0 | 10 | 11 | PASS |

This is **131 public theorems and 136 fresh axiom reports**. Every job built its
focused dependency closure with `lake --wfail build`, generated a fresh Lean
axiom transcript, matched the exact declaration inventory, and verified source
hashes, unchanged destination configuration and resolved dependency revisions.
Only `propext`, `Classical.choice`, and `Quot.sound` occur in the reports.

The source inventory was independently matched to every current Lean source.
All four downloaded artifact archives matched their GitHub SHA-256 digests:

- [Gaussian evidence](evidence/exact-gaussian-ff8e163/), job `139058006800`.
- [Cutoff evidence](evidence/exact-cutoff-ff8e163/), job `139058006434`.
- [Gram evidence](evidence/exact-gram-ff8e163/), job `139058006871`.
- [State-limit evidence](evidence/exact-states-ff8e163/), job `139058006920`.

The eight original mathematical Gaussian owners and all Lean sources in the
three other packages are unchanged. Independent source reviews are under
[reviews/20261125](reviews/20261125/). The actual staged source gate passed
before publication of the checked source snapshot. The final compiler
certificate is CI: a local Markov attempt was interrupted by executor recovery
and is not counted as a pass.

Post-validation edits update documentation, evidence and patch metadata only;
they do not change the checked Lean sources. These results certify the four
focused dependency closures, not the entire source or upstream repository.
Upstream main subsequently advanced to `a82aefbb07ff4fa1dd2e77ed8edaf7ec05547c04`
with manuscript-only changes; the prepared patches retain the tested `c25e77e`
base and the current upstream code remains identical in the affected packages.
The [final package check](evidence/package-ff8e163.json) matches every proposed
Lean file, including each umbrella, to the successful CI source inventory and
checks clean application of all four patches to both upstream revisions.

## Original exact destination results

All four jobs in GitHub Actions run
[45460909233](https://github.com/nickgou-nuke/info-geometry-lean/actions/runs/45460909233)
passed for preparation snapshot `4e0e4add51d44649cb232d9c8f540f26d34a709d`.
The original checked Lean sources are recorded by SHA-256. The new Gaussian
extension is tracked separately above.

| Contribution | Destination Lean / Mathlib | Public theorems | Fresh axiom reports | Result |
| --- | --- | ---: | ---: | --- |
| Matrix-weighted Gaussian elimination and integral composition | 4.34.0-rc2 / `8d52ea9a145a9255c4d301c0d1a1b8bf6e59305a` | 54 | 54 | PASS |
| Cutoff comparison and real power-log summability | 4.36.0 / `fc4f59e577feb1a4956671bc04ac18aaaf8cd842` | 16 | 16 | PASS |
| Complex finite Gram quotients and Hilbert colimit | 4.36.0 / `fc4f59e577feb1a4956671bc04ac18aaaf8cd842` | 27 | 29 | PASS |
| Positive compatible limits from summable state errors | 4.36.0 / `fc4f59e577feb1a4956671bc04ac18aaaf8cd842` | 10 | 11 | PASS |

These are 107 public theorems and three additionally audited definitions,
for 110 fresh axiom reports. Each job compiled the contribution and its
transitive imports with warnings treated as errors, generated a fresh axiom
transcript, checked the exact declaration inventory, matched source hashes,
and verified unchanged destination toolchain/dependency configuration and
resolved dependency revisions. The reports use no axioms beyond `propext`,
`Classical.choice`, and `Quot.sound`; some declarations are axiom-free.

The scope is the focused audit dependency closures, not a build of the whole
upstream repository or each umbrella library. Source and build evidence is in:

- [Gaussian evidence](evidence/exact-gaussian-4e0e4ad/)
- [Cutoff evidence](evidence/exact-cutoff-4e0e4ad/)
- [Gram evidence](evidence/exact-gram-4e0e4ad/)
- [State-limit evidence](evidence/exact-states-4e0e4ad/)

Each directory preserves the source inventory, build log, fresh audit,
dependency manifest/revisions, and an artifact receipt with the archive
digest and originating run. The original package check additionally matched every Lean file in each
original patch to that verified source inventory.
Documentation and packaging records updated after the run are not represented
as compiler-checked Lean source.

Earlier preliminary checks and failed intermediate destination runs remain
as historical evidence in this directory. Their results do not supersede
the successful run and source hashes above.

## Separate InfoGeometry adapter

The portable state-limit patch imports only Mathlib and its own generic
metric-limit module. The additional source-project adapter in
`followup/states/InfoGeometry/Canonical` targets the actual existing
`CStarStateColimit.Native.CompatibleStateFamily`, including compatibility for
all ordered pairs of stages. It is excluded from the upstream patch and the
CoreLean 4.36.0 job. Its local Lean 4.34.1 check and fresh one-theorem audit
passed. All five new state-limit/adapter files have zero warnings and errors;
14 inherited style warnings in unchanged source-project dependencies are
recorded separately. See the [local receipt](evidence/preliminary-states-followup/summary.json)
and [state theorem contract](../followup/states/THEOREM_CONTRACT.md).

This adapter follows the existing natural-indexed owner's `A : ℕ → Type`
universe signature. The portable theorem remains universe-polymorphic.
The adapter adds one public theorem and one audit report beyond the four
upstream packages. Including that separately checked adapter gives 132 public
theorems and 137 reports. It is not part of the new destination CI job, and the
locally repeated portable audit is not counted twice.

## Mathematical scope and corrections

Independent source reviews checked the following boundaries:

- The Gaussian matrix theory retains arbitrary rectangular maps and ordered,
  noncommuting products. The real density adapter proves normalization,
  elimination with determinant factors, the Schur determinant identity, and
  full normalized convolution for general positive-definite coarse precision.
- The scalar specialization retains the actual upstream coefficient
  `α * β / (β + s * α)`. The weighted adjoint uses the ratio of coarse to fine
  inner-product weights. A lattice scale already included in the adjoint is
  applied once in the normal operator. Both positive definiteness and the
  actual inverse-sandwich identity are proved for the noncommuting example.
- The cutoff recursion acts on the nonnegative cone. Real logarithmic
  exponents are supported. Summability and full-sequence convergence are
  proved with explicit relative-error constants and tails.
- The Gram construction keeps complex sesquilinear values, realizes finite
  nullspace quotients, and constructs a native `Module.DirectLimit`. The
  injections, density, and completion equivalence are proved. Finite-family
  stages use one fixed limiting kernel; the cutoff limit is a separate step.
- The state theorem proves complex linearity, positivity, normalization,
  exact compatibility, and quantitative tails. Approximate compatibility of
  arbitrary functions alone is not asserted to produce states. The hypothesis
  is a summable norm bound for every observable in each stage algebra, and
  refinements are unital star-algebra homomorphisms.

Gauge coercivity, actual uniform RG bounds, physical observable algebras and
refinements, and measure-level reflection positivity remain model-specific obligations.
General Markov averaging is not automatically a star-algebra homomorphism.
The original patches did not include a native Gaussian Markov-kernel/KL
adapter; the extension above supplies that separate interface.
No full Wilson-loop continuum or mass-gap theorem is claimed.

## Prepared publication

The [publishing directory](../publishing/) contains four independent patches,
their PR descriptions, focused upstream workflows, and a common axiom checker.
`prepared-prs.json` records the upstream base, task-owned local branches,
commit/tree identifiers, patch digests, and proposed file hashes. Each patch
starts from the same upstream base and preserves the original working tree.
The added Apache-licensed source carries its own license file.

**The upstream pull requests have not been opened.** The authenticated account
`nickgou-nuke` has read access but no push permission on the upstream repository.
No writable `nickgou-nuke/4D_Wilson_Loop_RG` fork was available. The connected
GitHub tools provide branch/commit/PR operations but no fork-creation operation;
the available browser currently reaches GitHub’s sign-in page before fork
creation. No authentication or fork creation has been completed in this turn.

Publication requires a writable
[fork of the upstream repository](https://github.com/MathePhysics/4D_Wilson_Loop_RG/fork)
accessible to the GitHub connection. Publication is already authorized; the
remaining requirement is technical access, not another approval of the work.
