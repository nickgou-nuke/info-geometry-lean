# Finite erasure and coarse-graining verification

## Acceptance status

This record separates source review, source gates, and native acceptance.
At preparation time, the new Lean sources have complete proofs and independent
source/API review. **Native compilation, zero-warning acceptance, and the
native declaration-axiom audit are pending.** They must not be inferred from
the source reviews or scans.

The publication branch is `codex/demon-rank-coarse-graining-20261117`, based on
`08c34e03f610b452e03422037949196dc7d92d6d`. The PR and its workflow bind the
published head explicitly; this source document cannot embed its own eventual
commit identifier without changing that identifier.

## Selected native targets

```text
InfoGeometry.Quantum.FinitePartialTrace
InfoGeometry.Quantum.MatrixTensorRank
InfoGeometry.Quantum.FiniteBathErasure
InfoGeometry.Quantum.PureAuxiliarySwap
InfoGeometry.Quantum.ProjectiveCoarseGraining
InfoGeometry.Probability.FiniteFluctuationBound
```

The five new owners contain **36 theorem declarations and one definition** by
source enumeration. The existing focused partial-trace owner gains one moved
theorem; its previous declarations remain. These are source counts, not the
count of declarations reported by Lean's native audit, which also sees
generated declarations.

Static parsing with `tools.quality.check_reviewed_prs.closure` records **60
repository modules** and **57 direct Mathlib source roots** for these selected
owners. Every source path exists at the recorded pin. The closure includes
the existing broad `Mathlib` import from a legacy dependency; this is not a
claim that the import set is minimal. The maintained checker compiles every
repository module in that closure from copied source.

## Independent source review

Separate reviewers inspected:

- Native tensor-map range/inclusion/flatness/finrank APIs and the basis
  transport to full matrix Kronecker rank.
- Both ordered positive-matrix support identities, unitary rank invariance,
  the mixed-system contradiction, and actual Gibbs normalization.
- The block-uniform channel on arbitrary full input matrices, zero projection
  blocks, readout identities, and every-finite-ancilla complete positivity.
- The existing likelihood IFT, finite negative-log Jensen and KL equality,
  the work ledger, correction sign, and saturation criterion.
- The namespace-preserving partial-trace lemma relocation and inspected
  consumers. Its statement and proof remain byte-identical.
- The exact coordinate-SWAP unitary and pure-auxiliary partial-trace boundary.

One concrete tactic repair from independent review removed an unnecessary
trailing `rfl` after a rewrite already closed the pure-projector goal. No
conclusion is added as an assumption to make a theorem pass.

The contract records mathematical hypotheses and remaining physical debt.
Source review is not native elaboration.

## Source gates

The following maintained gates are run sequentially against all seven changed
Lean owners: the six selected targets plus the legacy matrix-stage owner
from which the trace-adjoint theorem is moved.

```bash
python3 tools/quality/placeholder_audit.py --root OWNER --strict --json-out REPORT
python3 tools/quality/semantic_vacuity_gate.py OWNERS --fail-on error --json-out REPORT
python3 tools/infra/opengauss_screener.py OWNERS --strict --json
git diff --check
```

`OWNER`, `OWNERS`, and `REPORT` above stand for the exact paths recorded in the
publication evidence. The installed tracked pre-commit hook runs the staged
proof gate during the checkpoint commit. The PR records observed outcomes;
neither this command list nor installation of a hook alone is a pass.

Observed source-gate results at the prepared sources:

| Gate | Outcome |
|---|---|
| Placeholder audit on each of the seven changed Lean files | Exit 0 for all seven; zero hard findings. One soft automation-only finding concerns `blockUniformChannel_block_scalars`. |
| Semantic vacuity gate with `--fail-on error` | Exit 0, zero errors; two warning-level trivial-surface findings concern `blockUniformChannel_apply` and `blockUniformChannel_block_scalars`. |
| Strict OpenGauss screener | Exit 0, no violations or quarantined packets. |
| `git diff --check` | Exit 0. |

The reviewed warning-level surfaces are intentional API consequences: the
apply theorem unfolds the newly constructed linear map, and the block-scalar
theorem transports the independently proved fixed-projector law through
linearity and finite sums. The latter is consumed by the exact fixed-matrix
characterization. They do not assume the channel's positivity, trace law, or
complete positivity, and neither theorem is a proof placeholder. No scanner
rule or compiler warning is disabled to suppress these reports.

## Exact-head native workflow

[demon-erasure.yml](../.github/workflows/demon-erasure.yml) checks the published
pull-request head, not GitHub's synthetic merge commit. It:

1. Fetches the requested source SHA and verifies the unchanged Lean/Mathlib
   pins against the checkout.
2. Downloads or restores the Lean archive and verifies its fixed SHA256 even
   on cache hits; extracted executable caches are not trusted.
3. Fetches exactly the pinned Mathlib revision. Dependency artifacts may be
   cached; repository proof artifacts are never restored.
4. Computes the selected source closure, hydrates its existing native roots
   under the original shared build lock, and checks for active compilers.
5. Invokes the maintained native checker without incremental reuse or an audit
   skip, using a fresh output directory for this attempt.
6. Requires the report's source SHA and exact six-target list to match, all
   six selected owners to occur once, zero selected-owner warnings, successful
   compilation, and the native declaration-axiom audit.
7. Uploads reports, logs and exact source snapshots, including on failure.

The maintained audit enumerates declarations by their actual owner module,
so it includes the moved trace lemma even though its qualified namespace is
preserved. It rejects unsafe/partial declarations and any axiom outside
`propext`, `Classical.choice`, and `Quot.sound`.

The corresponding local checker command, when the recorded environment is
available, is:

```bash
python3 tools/quality/check_clifford_dirac.py \
  --mathlib-root ../pinned-mathlib \
  --lean ../lean-runtime/bin/lean \
  --output ../verification-demon-20261117/native \
  --target InfoGeometry.Quantum.FinitePartialTrace \
  --target InfoGeometry.Quantum.MatrixTensorRank \
  --target InfoGeometry.Quantum.FiniteBathErasure \
  --target InfoGeometry.Quantum.PureAuxiliarySwap \
  --target InfoGeometry.Quantum.ProjectiveCoarseGraining \
  --target InfoGeometry.Probability.FiniteFluctuationBound
```

This is a reproduction command, not a claim that it ran locally.

## Observed local and legacy boundaries

The original `/tmp/info-geometry-build.lock` was occupied at the nonblocking
preflight, with reported owner `clifford-dirac`, PID 6. No competing local
compiler, cache hydration, or build was started, and the lock was not deleted
or bypassed. The pinned Mathlib checkout lacked a hydrated `.lake` directory;
available workspace capacity was also constrained.

The separate legacy tower closure cannot currently be resolved by the scoped
checker: `InfoGeometry.Canonical.JordanKKTData` imports unresolved `Architect`.
That failure is outside the six selected targets. The unchanged moved lemma
and its namespace/import reachability were source-reviewed, but the complete
legacy tower is **not** counted as a successful native regression check.

The root Lake package also has unavailable external dependencies, including
`external_refs/homotopy-hypothesis-lean4` and `external_refs/atlas-lean`. This
change neither replaces their pins nor claims root-package acceptance.

## Evidence binding and publication

The local evidence directory `verification-demon-20261117` records intake and
candidate hashes, source-closure parsing, the original lock preflight, source
gate reports, and publication metadata. After publication, the head/tree and
every copied repository source are checked against the actual Git blobs.
Any future native report must bind those sources to that exact head before
its result is promoted.

The upstream submission is a draft PR for review. Publication is not a merge
or a native acceptance certificate. Pending CI is reported as pending.
