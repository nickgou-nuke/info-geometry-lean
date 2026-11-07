# InfoGeometry validation runbook

Source reviewed on 2026-11-03 against
`214f7bcf733eaf4720913bc2c082936f2480d3fc`. This page describes commands and
their coverage. It is not a fresh full-build certificate. Follow
[AGENTS.md](AGENTS.md) for proof acceptance and change policy, and the
[canonical pipeline](docs/CANONICAL_AGENT_PIPELINE.md) for optional integrations.

## 1. Establish the checkout and toolchain

Run from the current repository root. Inspect the commit, remote, and working
changes before editing. The pinned environment is defined by
[lean-toolchain](lean-toolchain), [lakefile.lean](lakefile.lean), and
[lake-manifest.json](lake-manifest.json). At the reviewed revision it uses
Lean `v4.34.1` and Mathlib revision
`d13f23b723b8a846827a245b89c10fc7d3f11612`.

Do not update dependencies to make a check pass without authorization.
Preserve existing build artifacts and follow the
[cache policy](WARNING_DO_NOT_RUN_CACHE.md) if an artifact is missing.
Inspect running compiler processes, keep builds/tests sequential, and use the
shared-lock wrappers. They reject linked Git worktrees and symlinked Lake
roots. Do not terminate a running Lake process without explicit user
authorization.

## 2. Select the coverage that the claim needs

| Check | Command or selection | What the result covers |
|---|---|---|
| One source file | `python3 tools/infra/run_locked_lean.py <file.lean>` | Elaboration of that file using the available imported artifacts |
| One module | `python3 tools/infra/run_locked_lake_build.py --wait-for-build-lock <Module>` | The specified Lake target and its dependencies |
| Changed owners | `python3 tools/infra/run_locked_lake_build.py --wait-for-build-lock --changed` | Changed owners selected by the helper; its default prefix is `InfoGeometry.` |
| Registered proof library | `python3 tools/infra/run_locked_lake_build.py --wait-for-build-lock proofs` | The `proofs` library selected in the root Lake configuration |
| Registered test suite | `python3 tools/infra/run_locked_lake_build.py --wait-for-build-lock InfoGeometryTestSuite` | The test roots listed for that library in the lakefile |
| All default targets | `python3 tools/infra/run_locked_lake_build.py --wait-for-build-lock --all-default-targets` | Every current `@[default_target]`, subject to the resulting build success |
| Ontology/phylogeny pipeline | `./scripts/run_pipeline.sh [--skip-lean-build]` | Narrow ontology/taxonomy Lean owners (unless skipped), Python taxonomy contract tests, `repo-phylogeny/v2` export + dashboard, and offline Auto-Ontology bridge dry-run |

The [Lake wrapper](tools/infra/run_locked_lake_build.py) also chooses
changed-owner mode when invoked without targets. A no-target success must not
be reported as a full build. `--wfail` requests warnings-as-errors. Extra Lake
flags go after `--` and are rejected in changed-owner mode.

The [lakefile](lakefile.lean) includes multiple libraries, explicit test roots,
and external entrypoints. Its default build is not a recursive certificate for
every tracked `.lean` file, mirrored repository, experiment, or archived
snippet. File counts and historical job counts do not establish coverage.

## 3. Representative owner targets and their actual scope

These paths replace the earlier unqualified unification claims. Read the
definitions and hypotheses before using a target's results:

| Lake target | Owner scope |
|---|---|
| `InfoGeometry.Projective.SplitOctonions.ZornMatrix` | [Reduced Zorn-coordinate multiplication](lean/InfoGeometry/Projective/SplitOctonions/ZornMatrix.lean) with a bilinear pairing; the defined product omits cross-product terms and supplies local diagonal-associativity results |
| `InfoGeometry.Projective.SplitOctonions.OctonionicProjectiveLine` | [Local associator lemmas and a projective-shell quotient](lean/InfoGeometry/Projective/SplitOctonions/OctonionicProjectiveLine.lean), with explicit coordinate hypotheses; the file does not establish a full motivic equivalence |
| `InfoGeometry.Projective.KuzminCuntzPath` | [Algebraic endpoint results and a conditional socket](lean/InfoGeometry/Projective/KuzminCuntzPath.lean); its star-ring equivalence is a supplied field, not a constructed C*-isomorphism |
| `InfoGeometry.OperatorAlgebra.KasparovKreinDIIIBridge` | [Concrete real 2×2 operator identities](lean/InfoGeometry/OperatorAlgebra/KasparovKreinDIIIBridge.lean), including square/anticommutation laws and vanishing left/right defects for the specified operator |

For example, the corrected Kasparov module target includes `OperatorAlgebra`:

```bash
python3 tools/infra/run_locked_lake_build.py --wait-for-build-lock \
  InfoGeometry.OperatorAlgebra.KasparovKreinDIIIBridge
```

A successful compilation of that module does not by itself prove a general
Class-DIII equivalence, an infinite-dimensional classification, or a physical
bulk-boundary theorem. The declared types determine what is established.

## 4. Mathematical and publication acceptance

For each changed owner, record its exact carrier, theorem statement,
assumptions, imported results, consumers, and unresolved implications. Check
that the proof establishes the reported statement without `sorry`, `admit`,
custom axioms, unsafe proof bypasses, `native_decide`, vacuous wrappers, or
unjustified replacement of noncommutative content. Review declaration axiom
dependencies and semantic scope separately from compiler success. The allowed
foundational axioms are `propext`, `Classical.choice`, and `Quot.sound`.

Install tracked hooks in a development checkout:

```bash
scripts/install_git_hooks.sh
```

The [pre-commit hook](.githooks/pre-commit) checks staged proof surfaces through
[the staged gate](tools/quality/proof_proxy_staged_gate.py). The
[pre-push hook](.githooks/pre-push) checks the relationship between the selected
commit and worktree and routes to
[scripts/quality/post_build_gate.sh](scripts/quality/post_build_gate.sh).
The latter has explicit incremental and full gate paths. Follow its actual
classification of the change; do not bypass it or replace a required gate with
a narrow file check. The existence of hook files does not show that they ran.

Source/debt scanners provide additional evidence, but their implementation
defines their coverage. For example,
[repo_lean_scope_audit.py](tools/quality/repo_lean_scope_audit.py) classifies
paths lexically; its labels are not a complete reconstruction of Lake's
target/import graph. Report scanner findings and build coverage separately.

## 5. Graph tools and optional execution support

Use [the deep-search protocol](docs/REPO_DEEP_SEARCH_PROTOCOL.md) and
[DAG wire-refactor workflow](skills/lean-dag-wire-refactor/SKILL.md) for graph
navigation and cleanup. Read candidate owners and their imports before
claiming redundancy or a missing bridge. GEPA, SymPy, Arango, and model output
can supply candidates or evidence; none replaces native Lean proofs.

The [canonical pipeline](docs/CANONICAL_AGENT_PIPELINE.md) documents current
Python entrypoints, guarded oracle adapters, optional service configuration,
the blocked root Pi launcher, and Archon's separate checkout prerequisite.
Do not infer successful runtime setup from a source file or old run report.

## 6. Completion record

Report the checked commit and toolchain, files/targets selected, exact commands
and exit results, axiom/placeholder/semantic checks, and unresolved failures or
unrun checks. Keep artifacts tied to their source revision. For documentation
changes, distinguish link/path/source validation from Lean compilation; do not
claim a fresh full build when none was performed.
