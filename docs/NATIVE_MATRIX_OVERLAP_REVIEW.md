# Native matrix spectral-sign integration review

Date: 2026-11-17. Main baseline `08c34e03f610b452e03422037949196dc7d92d6d`; stacked parent PR #395 at `7378582cd5a458a39a99ceb8720d04c5a14e3ac1`.

**Disposition:** independent source/mathematical review and all four scoped source checks pass. Fresh native compilation, zero target warnings, compiled declaration-axiom acceptance, and root-package/pre-push integration remain outstanding. The maintained shared build lock is occupied by another build and has not been bypassed. This is a draft source checkpoint.

## Current source identities

| Owner | SHA-256 |
|---|---|
| `MatrixSpectralSign.lean` | `d6ca43fa50c5913f35542c5f22a48648b316203956edb83457b0c6fb68a79aa2` |
| `MatrixOverlapDirac.lean` | `f2805069893b87636d3c6b5c7524f224d92c3833075d2407d6f8f0e1b7fff2b3` |

Lean remains `v4.34.1`; Mathlib remains `d13f23b723b8a846827a245b89c10fc7d3f11612`. The supplied paper is unchanged; its identity and version-specific primary links are in [the provenance record](sources/native_matrix_overlap_20261117.json).

## Concurrent ownership and exact reuse

The original owner search covered 37 open PR heads at 13:54:55 UTC. PR #395 was published at 13:57:14 UTC and discovered in the final remote refresh. Its actual sources were read before revising this draft. Its `OperatorAlgebra/GinspargWilson` already owns the generic algebra, so the initial competing `Algebra/OverlapDirac.lean` was removed. The two remaining new owners construct the actual sign and integrate it with that existing owner. The complete search record, including the superseding discovery, is [here](NATIVE_MATRIX_OVERLAP_OWNER_SEARCH.md).

The parent commit's six changed file blobs, complete tree and commit object were independently reconstructed and checked against GitHub. Its files and all other inherited owners are retained unchanged. The local branch integrates both original draft and parent histories; publication uses the corresponding parent commits and does not rewrite the prior draft checkpoint.

The explicit constructed `negativeSignInvolution` has `chi = -spectralSign H` and obtains `chi_sq` from native CFC. This is an input to the existing `ChiralInvolution` owner, not an assumed sign law. The compatibility theorems identify upstream `1 - gamma.chi * epsilon.chi` with `1 + Γ * sign H`, and upstream `epsilon.Pright` with the actual positive spectral projector. GW, idempotence, and intertwining call the existing `overlapDirac_ginspargWilson`, `Pright_idem`, and `overlapDirac_mul_Pright` declarations.

## Independent mathematical/source review

Generation and review were separate. Review checked the pinned Mathlib CFC signatures, finite-spectrum continuity, the exact equivalence between sign-square-one and invertibility for Hermitian inputs, the native spectral expression, the involution fixed-point theorem, and commutant preservation. Real and complex full matrix algebras are supported; the empty-index case is not silently ruled out.

The revised bridge was independently read in full against #395's exact source. Ordered products and both minus signs in the convention map are retained. No commutation of Γ and H is assumed. The stronger arbitrary-kernel adjoint and modified-sign statements keep their original hypotheses through direct matrix proofs; no invalid involution is constructed outside the Hermitian-invertible domain. The other old matrix statement names and hypotheses remain intact.

The concrete real pair `Γ = diag(1,-1)`, `H = [[0,1],[1,0]]` satisfies an explicit ordered-product inequality and evaluates the actual CFC-based D to `[[1,1],[-1,1]]`. The separate theorem `IsUnit (-Γ) ∧ D(Γ,-Γ)=0` distinguishes kernel invertibility from possible overlap zero modes. The examples were retained through integration.

## Executed source checks

The exact receipt is `verification/matrix-overlap-reuse395-source/receipt.json` in the task workspace. Both strict `placeholder_audit.py --root <owner> --strict --json-out <report>` commands, the two-file `semantic_vacuity_gate.py --fail-on error`, and strict two-file `opengauss_screener.py --json` exited zero.

Both placeholder audits scanned one file and report zero hard findings. The spectral owner retains one disclosed soft short native-CFC specialization finding; the matrix owner has no placeholder findings. The semantic report covers both selected/read files without read failures and has one advisory on the explicit `positiveSpectralProjector_eq_modifiedMinus` formula. That theorem consumes the actual chirality-square hypothesis through the proved modified-sign identity. It is retained as a useful compatibility statement. OpenGauss reports no violations or quarantine packets. No checker or threshold is changed to suppress these findings.

The normal commit invokes the installed staged hook; its actual result and publication identities are recorded in the PR metadata. Source checks are distinct from Lean elaboration and compiled axiom checks.

## Closure and dedicated workflow

The maintained resolver gives **11 repository modules**, including **2 target owners** and **9 dependencies**, with **5 direct native Mathlib import roots**. The inherited GW and chiral-involution owners are in that actual closure. Only these two new owners are the target-warning/source/owned-declaration scope; every dependency is freshly compiled and all transitive axiom dependencies of the owned declarations are checked. Parent #395's other two new owners are outside this narrower import closure and are not certified by it.

The workflow [native-matrix-overlap-dirac.yml](../.github/workflows/native-matrix-overlap-dirac.yml) has SHA-256 `454e53d52272f0062bf1c6ad915bd79c1c6ed6dc5689c28d20580ac0cfab0af8`. It verifies the exact event revision and unchanged pins, freshly compiles the whole resolved closure, forbids reused project outputs, requires zero target warnings, and audits every owned declaration. The only permitted axioms are `propext`, `Classical.choice`, and `Quot.sound`; unsafe/partial declarations are rejected.

All source/live-copy hashes, exact declaration counts, complete source-gate coverage, and 18 helper/pin/workflow/document/provenance inputs are bound into uploaded evidence. All eleven maintained helper files remain unchanged from main. The three-target initial workflow was updated consistently to two targets in its environment and both count assertions. YAML, all seven Bash blocks, and all five embedded Python blocks are syntax checked for the revised workflow. Evidence uploads even on failure.

Actual nonblocking probes of the maintained shared lock found it busy. No competing local compiler or cache operation was started. A queued hosted run is not native acceptance, and evidence from the superseded initial draft must not be transferred to the revised source. Root-package/pre-push and broader integration gates remain separate.

## Interpretation boundary

The implemented layer is pointwise finite spectral calculus and the chirality identities in paper equations (2.6)--(2.9). It does not construct Wilson links, uniform family gaps, differentiability, locality, comparison currents, Kato ODE transport, determinant phases, a global measure, or an interacting continuum theory. Complex determinant-phase information must be retained in any later realification; the current theorems support the complex matrix carrier directly.

The paper's author already supplies a larger Lean companion, described in the primary verification report. Its source archive was not inspected or replayed here; its reported results are external evidence on a newer toolchain. This branch makes a distinct, limited repository-integration claim.
