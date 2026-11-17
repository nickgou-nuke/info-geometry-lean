# Native matrix spectral sign and overlap Dirac review

Date: 2026-11-17. Baseline: `08c34e03f610b452e03422037949196dc7d92d6d`.

**Disposition:** independent source and mathematical review and all five scoped source checks pass. The final source is a draft candidate: native compilation, zero target warnings, the compiled declaration-axiom audit, and root-package/pre-push integration acceptance remain outstanding. The maintained shared build lock is occupied by another build; it is not bypassed. Hosted execution is required to obtain a fresh native result.

## Exact source identities

| Owner | SHA-256 |
|---|---|
| `MatrixSpectralSign.lean` | `d6ca43fa50c5913f35542c5f22a48648b316203956edb83457b0c6fb68a79aa2` |
| `OverlapDirac.lean` | `7f97ea324fe187b3a71f3142d3f58f11447af14a86606046116f2aea4ed38cfa` |
| `MatrixOverlapDirac.lean` | `000703c45e08c074cd6077ebd89ad4dce219d16fe2ace928e6996a080a2245f9` |

The paper's exact attachment identity and immutable version links are in [the source provenance](sources/native_matrix_overlap_20261117.json). No toolchain or Mathlib pin changes are made: Lean `v4.34.1`, Mathlib `d13f23b723b8a846827a245b89c10fc7d3f11612`.

## Owner search and scope selection

The [bounded source ledger](NATIVE_MATRIX_OVERLAP_OWNER_SEARCH.md) records actual declarations, imports, hypotheses, consumers, and all 37 open PR heads inspected on 2026-11-17. Main already owns Kato-generator tangent recovery, Peirce odd-product routing, cyclic off-diagonal trace cancellation, and faithful arbitrary-index realification. The initial possible tangent-trace contribution was therefore not promoted as new mathematics. The search did not locate the general native matrix spectral-sign/overlap integration now proposed. This is a bounded repository-gap result, not a claim that the paper's larger formalization is absent.

`CyclotomicOperatorProjectors` already owns the noncommutative half-projector laws. The algebra layer reuses those theorems with `algebraMap ℝ A (1/2)`, whose commutation is intrinsic to scalar multiplication. No commutation between `Γ` and `ε`, or between `Γ` and `H`, is assumed. Both inherited repository dependencies remain unchanged.

## Independent mathematical and API review

The spectral sign was generated and independently reviewed against the exact pinned Mathlib declarations. The construction is actual `cfc Real.sign H`, using the finite Hermitian matrix spectral theorem internally. Finiteness supplies continuity on the spectrum. Invertibility is needed for the sign to square to one, not supplied as an unproved sign-law field. The exact converse, a Hermitian-involution fixed-point theorem, and preservation of an arbitrary commutant were reviewed as well. Empty finite index types are allowed without a false nontriviality assumption.

The overlap algebra was independently reviewed with ordered products intact. Its carrier is an arbitrary associative ring; adjoint identities add star hypotheses and half-projector identities add a real algebra. Modified chirality is `-ε`, so the modified negative projector selects the positive sign. The matrix layer discharges the generic spectral-involution premise from the actual Hermitian invertible input.

The concrete real example uses `Γ = diag(1,-1)` and `H = [[0,1],[1,0]]`. It proves an explicit ordered-product inequality and computes the actual CFC-based operator as `[[1,1],[-1,1]]`. A second theorem proves `IsUnit (-Γ)` and `D(Γ,-Γ)=0`; invertibility of the kernel therefore does not justify assuming invertibility of the overlap operator. The full result also applies to complex matrices. No trace projection or scalar replacement is used.

The independent review examined the final half-scalar calculation and Hermitian-projector theorem. Integration added explicit closing commands for the noncomputable sections. The source screener did not recognize the initial `¬ Commute` formulation of the concrete witness; it now states the equivalent explicit matrix-product inequality, retaining its entrywise proof. The screener and its thresholds are unchanged.

## Actual source checks

The receipt at `verification/matrix-overlap-source/receipt.json` in the task workspace records the exact hashes above and these executed commands, each at exit zero:

- Strict `tools/quality/placeholder_audit.py` on each of the three owner paths, using `--root <path> --strict --json-out <report>`.
- `tools/quality/semantic_vacuity_gate.py <all three paths> --fail-on error --json-out <report>`.
- `tools/infra/opengauss_screener.py --strict --json <all three paths>`.

Each placeholder audit read one file, with zero hard findings. The spectral owner has one disclosed soft short-proof finding around its direct native-CFC specialization; its referenced Mathlib theorem and proof were inspected. The other two owners have zero findings. The semantic report records all three selected and read files, complete coverage, no read failures and no findings. Strict OpenGauss reports no violations or quarantine packets after the equivalent witness formulation. These are source results, not native elaboration or compiled axiom acceptance.

## Native closure and workflow

The maintained resolver returns five repository modules: the three targets, `Algebra/FiniteSpinAlgebra`, and `Algebra/CyclotomicOperatorProjectors`. Five direct Mathlib roots are resolved. The inherited cyclotomic owner imports the full `Mathlib` umbrella. Its historical proof scripts and the cost of that cache remain visible; the dependency is neither replaced nor speculatively edited.

The dedicated workflow is [native-matrix-overlap-dirac.yml](../.github/workflows/native-matrix-overlap-dirac.yml), SHA-256 `cfdeaee1a8c5dadc3ddaff0c665a0c87a471de9720be556ab10dbb9a8e56fe46`. Independent review checked its fresh exact closure, absence of project-output reuse, zero warnings for all three targets, and compiled enumeration of every declaration owned by each target. Only `propext`, `Classical.choice`, and `Quot.sound` are permitted; unsafe and partial declarations are rejected.

The workflow checks the exact public event SHA, unchanged pins and verifier inputs, every live/copied closure source hash, exact audit counts, and complete source-gate coverage. Eighteen helper/pin/workflow/document/provenance inputs are bound into the final artifact. All eleven maintained helper files match main byte-for-byte. Evidence uploads even on a failed native stage. YAML parsing, all seven Bash blocks, and all five embedded Python blocks passed syntax review; the added owner-search input is included in trigger, checkout and integrity lists.

A fresh nonblocking `BuildLock(..., block=False)` probe observed the maintained shared lock busy. No local compiler, cache download, or competing build was started. The installed staged hook is executed by the normal commit operation; its actual outcome and publication identities are recorded in the PR body. Source review and syntax checks do not substitute for a successful native run.

## Interpretation boundary

This is the finite pointwise sign/chirality layer in paper equations (2.6)--(2.9). It does not construct the Wilson operator from links, a volume-uniform interpolation gap, differentiable spectral families, exponential locality, the comparison current, determinant transport, a fermion measure, or an interacting continuum theory. Section 5 requires complex determinant-phase data; an eventual real-only treatment must retain the internal complex structure and a phase-weighted trace.

The author already supplies a much larger Lean companion. Its primary verification report records 16 compiled modules and a separate kernel replay on Lean `v4.35.0-rc2`; it also records six native lint findings and an unsuccessful frozen-reference Comparator run, distinct from the reported successful proof checks. The source archive was not inspected or replayed here. This branch claims neither ownership of that development nor independent verification of its global conclusions.
