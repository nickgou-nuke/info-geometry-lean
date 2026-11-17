# Hodge–commutant source review and verification record

Review date: 2026-11-17. Scope: the five owners in [HODGE_COMMUTANT_CONTRACT.md](HODGE_COMMUTANT_CONTRACT.md), the recovered intake, and the proposed dedicated workflow.

**Current disposition:** source review passed; scoped static checks and the installed pre-commit gate passed at the recorded scope. Fresh native closure and declaration-axiom acceptance remain pending. Remote workflow execution has not been certified. Publication is authorized as a draft with these limitations disclosed.

## Baseline and intake provenance

- Baseline commit: `08c34e03f610b452e03422037949196dc7d92d6d`.
- Intake: [sources/hodge_commutant_intake_20261116.txt](sources/hodge_commutant_intake_20261116.txt).
- Intake SHA-256: `12f8529e51f534c71e33d0f087b95cb6628cb3fbe2459bbe9b57dbbaa140e603`.
- Original attachment name: `Pasted text(20261116-182549).txt`.
- Lean `v4.34.1` and Mathlib `d13f23b723b8a846827a245b89c10fc7d3f11612` remain the dependency pins.
- The prior transient workspace expired. Its development logs and compiler artifacts are absent; none were manufactured during recovery.

The intake is retained as input provenance. Its proposed axioms, metaphors, named “deductions,” and uniqueness claims have not been accepted merely because they appeared in that text.

## Source identity and recovery classification

| Owner below `lean/InfoGeometry/` | Current SHA-256 | Classification |
|---|---|---|
| `OperatorAlgebra/NoncommutativeKrausChannel.lean` | `62091573510385b10a7678bbdca99c4cbf62737e1bf9b8e60728e62abc30ed45` | Semantic reconstruction |
| `Physics/RegularBimoduleCommutant.lean` | `a85dd111963c5ec1077069a5d2e2aa91d782e29c739690466a09854288bec6f4` | Exact recovery |
| `Quantum/KrausUniversalFixedEffects.lean` | `19df4a3b98c871e37cfcfddc7ca3fcb30145c4d7d0258a05a5839c463e71c9ca` | Exact recovery |
| `OperatorAlgebra/MatrixCommutatorHodge.lean` | `c67fbceea6410b341b862b360508b550ecb28cd72b680f5d3f555a7bc6ffc092` | Exact recovery |
| `Quantum/BipartiteOperatorSectors.lean` | `ec425286d6b824588705a1e5837bfb638d5b2171870ef5aecdf01fb1dfd71d6b` | Exact recovery |

The generic baseline was fetched at the exact baseline commit. Its standalone baseline SHA-256 is `d11b4db5ae54468ec5972d5f2806f942646abc6b81400537fd6f0115f7df1699`. Only the five-theorem insertion was reconstructed.

The prior complete generic source hash was `1ed0688394c1b3d073f2b0cc2f51c6c8c4f5c26f6411468e1f837aa257ed08d8`. The current `62091573…` source is not byte-equivalent to it. The defect theorem's retained simplification proof was restored; other short proof text and comments were reconstructed. All five retained names, generic ring/star-ring hypotheses, ordered completeness, quantifiers, and conclusions were preserved.

Independent source review found no weakening or API-scope change in that reconstruction. The pinned Mathlib center definition was checked: membership supplies `IsMulCentral.comm`, supporting the restored `hE.comm` proof. The existing graded-trace import supplies `Mathlib.Tactic`, including `abel`.

Matching a historical hash establishes source identity. It does not establish that the recovered source compiled previously or now. No historical generic development pass is being transferred to the new hash.

## Semantic review of the actual propositions

| Area | Source-level assessment |
|---|---|
| Generic Kraus identities | Full arbitrary `Ring`/`StarRing` content retained. Associativity and distributivity expand the ordered defect; commutation is a sufficient fixedness condition. |
| Regular commutant | Actual `LinearMap` left/right actions are used. Right-action conservation requires completeness, not a postulated Hodge law or an unidentified Hilbert adjoint. |
| Hodge construction | `PiLp 2` is the finite Hilbert product. The adjoint-generator commutator has the correct sign. The default kernel is a joint centralizer; ordinary algebra generation is explicitly required for the center. |
| Matrix universal converse | The complete matrix-unit reset family separates nonscalar observables. The quantifier includes the matrix-index family; it is not a fixed-instrument converse. |
| Hodge/Kraus bridge | `fixed_by_all_kraus_iff_laplacian_eq_zero` uses the actual center and native linear-map kernel, with `Algebra.adjoin = ⊤` and nonempty matrix index. |
| Scalar counterexample | The explicit `Mat2C` witness includes PSD normalization, effect bounds, unitarity, noncommutation, nonzero operator defect, and zero scalar anomaly. |
| Four sectors | Concrete Hilbert–Schmidt submodules, a constructed linear equivalence, scalar intersection, and dimensions are retained. Vectorization includes the required transpose, and `operatorEquiv_mul` preserves arbitrary operator multiplication. |
| Interpretive limits | No higher nilpotence, entanglement criterion, weighted-GNS identification, global history conservation, Type III limit, or physical uniqueness theorem has been smuggled into the finite statements. |

The detailed intake corrections and missing implications are recorded in the contract. In particular, “nonzero commutator” and “nonzero scalar anomaly” remain different claims, and the mixed sector is not defined as the set of entangling operators.

## Fresh scoped source checks

The following results were read from the current receipt and reports under
`/workspace/scratch/a6c715447467/verification/source/`. That receipt records the five current source hashes above and seven successful command invocations.

| Check | Observed current result | Authority |
|---|---|---|
| Strict placeholder audit, once for each of five owners | All five commands exited `0`; each scanned one selected file; total hard findings `0`, total soft findings `4` | Lexical/source heuristic |
| Semantic-vacuity gate with `--fail-on error` | Exit `0`; selected `5`, read `5`, coverage complete, no read failures; errors `0`, warnings `10` | Lexical/source heuristic |
| Strict OpenGauss screener on all five owners | Exit `0`; `violations: {}`; `quarantined_packets: []` | Scoped source screener |
| Installed pre-commit hook | Executed with exit `0` and `proof_proxy_staged_gate: ok` | Staged source gate, not a native certificate |
| Independent source review | Current five hashes, seven source commands, warning dispositions, and workflow scope reviewed; no source blocker reported | Human-readable proposition/implementation review |

The command families recorded in the receipt are:

```text
python3 tools/quality/placeholder_audit.py --strict --root <owner> --json-out <report>
python3 tools/quality/semantic_vacuity_gate.py <five owners> --fail-on error --json-out <report>
python3 tools/infra/opengauss_screener.py --strict --json <five owners>
```

These are descriptions of the actual recorded command families, with paths abbreviated here. They do not claim repository-wide coverage. Zero hard heuristic findings is not a proof of axiom cleanliness.

### Disposition of nonblocking findings

The four placeholder soft findings concern `krausDual_add`, `krausDual_eq_krausMap_star`, `kronecker_bimodule_action`, and `operatorEquiv_apply`. They flag short automation or definitional proofs; they do not report proof holes. Source review checked their actual conclusions and referenced operations.

All ten semantic-gate warnings are `trivial_surface` findings:

- Definitional application lemmas: `differential_apply`, `leftAction_apply`, `rightAction_apply`, `leftLift_apply`, `rightLift_apply`, and `operatorEquiv_apply`.
- Short algebraic or native-API bridges: `krausDual_add`, `star_leftAction_star`, `kronecker_bimodule_action`, and `krausDual_eq_krausMap_star`.

Their role is to expose computed definitions or connect existing native operations. The substantive center, universal-converse, counterexample, orthogonal-decomposition, and dimension claims are separate declarations. Warnings are disclosed, not suppressed or relabeled as a kernel pass.

## Dedicated workflow review

The initial reconstructed `.github/workflows/hodge-commutant.yml` had reviewed source SHA-256
`8f6262cd8aa694c3416776a4f2f34edda41f49f85645913e5ededb88ecc2f05b`.
The current checkout-repaired workflow has SHA-256
`495ae8b5eb4a7f4d21b5873218f6765faca9f5799ac27d9eaf7298bdbc916acc`.

Its static review parsed the YAML and five embedded Python blocks. Independent review confirmed the selected five owners' complete 18-module project import closure and preservation of verification inputs. The workflow uses the repository pins and maintained closure/axiom machinery, preserves source reports, and binds scoped reports to the kernel evidence it is intended to produce.

This workflow was reconstructed from the committed baseline template and current helper interfaces; no old workflow hash exists. YAML parsing and Python syntax checks do not mean that GitHub Actions ran successfully.

### Observed hosted checkout failure and repair

[The initial dedicated run](https://github.com/nickgou-nuke/info-geometry-lean/actions/runs/44045173114)
failed in `actions/checkout@v4` before the Lean installation or proof checks began.
The action's credential-removal phase invoked `git submodule foreach --recursive`,
which failed because `external_refs/auto-ontology` has no URL in `.gitmodules`.
That gitlink and missing mapping already occur at the recorded baseline. No
native result or evidence artifact was produced by this failed run.

The repair changes only the initial project checkout. It initializes an independent
Git repository, fetches the exact public `GITHUB_SHA` without credentials or recursive
submodule operations, checks out a detached head, and requires exact SHA equality.
Its sparse paths include all canonical Lean sources, tools, pins, workflow, and
provenance documents. Sparse checkout alone does not fix the credential-cleanup
failure; avoiding that unnecessary traversal is the operative change.

Independent review checked Bash syntax, all five Python blocks, all 18 resolved
project imports, and all 14 verification inputs. Every subsequent workflow step,
permission, event, and verification threshold is unchanged. The five Lean source
hashes and the source-check receipts above remain unchanged. A fresh hosted run
of the repaired workflow is still required for native acceptance.


## Native acceptance and publication status

| Gate | Status at this review snapshot |
|---|---|
| Fresh five-owner native import-closure check | Pending; the maintained check is queued under the shared build lock |
| Fresh declaration-axiom audit | Pending with the native check |
| Allowed axioms restricted to `propext`, `Classical.choice`, `Quot.sound` | Acceptance requirement; no fresh result claimed |
| Native warnings or errors for the restored five-owner closure | No final current result recorded here |
| Remote workflow run for the published head | Initial run failed before Lean; repaired checkout awaits a fresh native result |
| Draft publication | Authorized; publishing a draft does not change any verification status above |

A fresh run directory is designated `verification/final-integrated` in the current workspace. A queued process, an empty log, or a prepared output directory is not a successful native check. Update this record using the actual completed receipt and the exact checked source hashes.

There is no claim of a successful full-repository build. Historical development messages are context only; the missing original logs cannot establish completed coverage, zero target warnings, or axiom acceptance.

## Completion instructions for the integrator

1. Keep this review tied to the exact published source bytes. If proof repairs change an owner, record its new hash and rerun the affected current checks.
2. Complete the maintained native closure and axiom audit using the unchanged pins and shared build lock.
3. Preserve actual receipts and report all target diagnostics at their observed scope.
4. Record the remote workflow result against the actual published commit; do not infer it from local static checks.
5. Keep the PR in draft, with pending gates disclosed, until the required acceptance evidence is available.

The mathematical scope remains the finite and generic statements in the contract regardless of whether these gates later pass. Successful Lean checking will certify those propositions, not the stronger continuum and physical claims rejected from the intake.
