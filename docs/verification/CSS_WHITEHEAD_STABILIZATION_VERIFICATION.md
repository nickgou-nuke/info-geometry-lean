# Whitehead stabilization and stable presentation verification

## Result and scope

The fresh independent native verification **passed** at source checkpoint
`abd22cd4badf6df017cc85fa137cb2160f48eca9`, based on main
`a392af178af1fe2bcba2ba39eb405700c6ee103c`. The checked source checkpoint tree is
`c3be031ec27e795572eb35eb0b25f46dff13f968`.

The five new owners contain **81 named theorems and 146 native declarations**.
The audit also covers **25 declarations** in the unchanged Krein owner, for
**171 declarations** in total. All six modules were freshly compiled with
zero warnings and no incremental reuse. The only foundational axioms found
were `propext`, `Classical.choice`, and `Quot.sound`.

The maintained root build and actual new-ref pre-push hook both **exited 1**:
the configured path package `external_refs/homotopy-hypothesis-lean4` is absent.
This record supports a draft for review and preservation. It does not certify
the canonical aggregate, full repository, or publication-gate acceptance.
Remote CI results are recorded separately in the PR after observation.

## Mathematical acceptance

The [contract](../CSS_WHITEHEAD_STABILIZATION_CONTRACT.md) records the exact
source, native carriers, theorem dependencies, and scope. The source is
arXiv:2608.09913v2, Section VII.1.2, Definitions 13–14 and Proposition 1.

The construction supplies actual scalar-entry elementary units, block-shear
membership in their generated subgroup, the ordered Whitehead factorization,
and explicit identity-block and zero-row stabilization equations. It proves
ordinary/elementary coincidence separately for move-generated stable
presentations and for the paper's one-shot identity/zero-padding formulation.
The latter uses canonical finite-index casts and native Sigma equality;
arbitrary row permutations are not inserted into the definition.

The companion inverse-adjoint homomorphism and hyperbolic lift preserve both
off-diagonal forms and the full ordered rectangular pairing. Coefficients are
arbitrary `Ring`; adjoint statements add `StarRing`. Empty dimensions are
allowed. Only the concrete noncommutativity witness requires `Nontrivial`.
No physical circuit, locality, superselection classification, Ext comparison,
Koszul nonsplitting, or analytic limit is asserted. The two stable formulations
are not claimed to be related by a general normal-form theorem.

## Independent checks

| Check | Observed result |
|---|---|
| Exact repository source closure | Six modules freshly compiled, zero warnings |
| Native declaration axiom audit | 171 declarations; permitted foundational axioms only |
| Strict placeholder scans | Six exit-0 commands; zero hard findings, 11 soft findings |
| Strict semantic scan at warning threshold | Exit 1; 18 reviewed warnings, zero errors |
| Raw banned-proof-token scan | No matches in the six selected owners |
| Existing Krein source and dependency pins | Byte-identical to base |
| Actual source-checkpoint pre-commit hook | Passed |
| Maintained root Lake wrapper | Exit 1 during package initialization |
| Actual new-ref pre-push hook | Exit 1; build blocked, subsequent static checks passed |

All 29 heuristic findings have individual dispositions in the
[independent acceptance](css-whitehead-stabilization/independent-acceptance.md)
and [machine review](css-whitehead-stabilization/findings-dispositions.json).
They concern definitional coercions, genuine identities proved through native
simplification, and unchanged Krein facts. Their review does not turn the
strict semantic command's nonzero exit status into a pass.

Lean is `leanprover/lean4:v4.34.1`; Mathlib is pinned to
`d13f23b723b8a846827a245b89c10fc7d3f11612`. Verification used the shared build
lock. All nine inspected native dependency revisions match their manifests.
The pre-existing Batteries `docs/README.md` type change was inspected and
preserved; no dependency Lean-source change was observed or made. Native
caches were used, so this is not a source rebuild of every dependency package.

## Reproduction

From the repository root, the independent command was:

```bash
python3 tools/quality/check_clifford_dirac.py \
  --mathlib-root /workspace/scratch/66380c6bf432/info-geometry-lean/.lake/packages/mathlib \
  --lean /workspace/scratch/4796737fb777/lean-environment/lean-4.34.1-linux/bin/lean \
  --target InfoGeometry.Algebra.ElementaryMatrixOperators \
  --target InfoGeometry.Algebra.WhiteheadStabilization \
  --target InfoGeometry.Algebra.StablePresentationEquivalence \
  --target InfoGeometry.Algebra.StablePaddingEquivalence \
  --target InfoGeometry.Algebra.HyperbolicPresentationTransport \
  --target InfoGeometry.Canonical.SpinorialCore.KreinAdjoint \
  --output /workspace/scratch/d18a558d1d7d/css-rigidity-qa
```

This exited 0 without incremental reuse or audit-skipping flags. The absolute
paths describe the observed run; another machine must provide its own paths
at the same pins. The dedicated workflow obtains the pinned native imports,
runs the maintained checker, and explicitly asserts zero warnings for every
target. Its semantic gate fails on errors and preserves warnings. The
independent local review additionally used the warning threshold and retained
its exit-1 result.

## Root integration and tracked hook

The actual root command was:

```bash
python3 tools/infra/run_locked_lake_build.py --wait-for-build-lock \
  InfoGeometry.Algebra.StablePaddingEquivalence \
  InfoGeometry.Algebra.HyperbolicPresentationTransport
```

It exited 1 with `HomotopyHypothesis: package directory not found`. The command
initialized the configured pinned Mathlib and LeanCopilot checkouts but did
not reach elaboration of the requested owners.

The actual `.githooks/pre-push` was then invoked for a new remote ref at the
source checkpoint. Its comparison base was the GitHub-verified main revision,
recorded in the local `origin/main` tracking ref. The hook's incremental build
selected all five new owners and `Canonical.All`; it encountered the same
missing package. Its axiom/debt text scan, semantic-content audit, tracked
scope audit, and quarantined-artifact audit passed. The overall hook exited 1.
The hook's later full-root-gate step was not reached.

No dependency pin, gate implementation, or threshold was changed to remove
this failure. Root-package initialization is outside the independently
successful source-closure check. Draft preservation under the user's standing
publication instruction does not imply merge readiness.

## Preserved evidence

| File | Contents |
|---|---|
| [source-closure.json](css-whitehead-stabilization/source-closure.json) | Exact source graph, hashes, compiler results, native counts and axiom union |
| [axiom-audit.txt](css-whitehead-stabilization/axiom-audit.txt) | Complete declaration-level native audit |
| [native-logs.json](css-whitehead-stabilization/native-logs.json) | Module logs, generated native audit source, environment, original evidence manifest |
| [static-gates.json](css-whitehead-stabilization/static-gates.json) | Exact static commands, outputs, source comparisons and dependency state |
| [placeholder-findings.json](css-whitehead-stabilization/placeholder-findings.json), [semantic-findings.json](css-whitehead-stabilization/semantic-findings.json) | Complete heuristic reports |
| [root-build.json](css-whitehead-stabilization/root-build.json), [root-build.txt](css-whitehead-stabilization/root-build.txt) | Root wrapper arguments, exit status and raw log |
| [source-pre-push.json](css-whitehead-stabilization/source-pre-push.json), [source-pre-push.txt](css-whitehead-stabilization/source-pre-push.txt) | Actual hook arguments, stdin, exit status and raw log |
| [source-checkpoint.json](css-whitehead-stabilization/source-checkpoint.json), [source-commit.txt](css-whitehead-stabilization/source-commit.txt) | Source checkpoint and actual pre-commit result |
| [evidence-sha256.json](css-whitehead-stabilization/evidence-sha256.json) | Hashes of the preserved evidence and this overview |

A documentation-only evidence commit follows the checked source checkpoint.
All six repository-source hashes and all maintained native-verifier hashes
are reconciled before recording that evidence. Acceptance is tied to those
exact source hashes. Registering imports in `Canonical.All` does not certify
that aggregate or downstream consumers outside the selected closure.
