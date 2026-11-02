# Getting started with a scoped Lean check

> Status: `maintained local guide`
> Source reviewed: 2026-11-03 at `214f7bcf733eaf4720913bc2c082936f2480d3fc`.
> Commands below follow the inspected source interfaces. This guide does not
> claim that a fresh checkout or full build was executed during the review.

## 1. Select the checkout and pinned toolchain

Use Git, Python 3, and an installed Lean/Elan toolchain manager. Start from an
independent checkout of the intended repository:

```bash
git clone https://github.com/nickgou-nuke/info-geometry-lean.git
cd info-geometry-lean
git remote -v
git rev-parse HEAD
cat lean-toolchain
```

For an existing checkout, use its root (`git rev-parse --show-toplevel`) and
inspect `git status` before editing. The maintainer workstation path is not a
portable prerequisite. Read [AGENTS.md](../AGENTS.md) and the
[canonical pipeline](CANONICAL_AGENT_PIPELINE.md) before running builds.

Install the exact toolchain named by `lean-toolchain` through Elan if it is
missing. Do not change `lean-toolchain`, `lake-manifest.json`, or dependency
revisions to make a local build proceed. The reviewed baseline uses Lean
4.34.1 and the Mathlib revision recorded in
[lake-manifest.json](../lake-manifest.json).

## 2. Check local dependencies before compiling

The root Lake package includes path dependencies. In the reviewed manifest,
these include `lib/InfoGeometryCore`, `external_refs/gift-framework-core`, and
`external_refs/atlas-lean`. Other external owner families are exposed by
[lakefile.lean](../lakefile.lean); a target can have additional prerequisites.

The maintained preflight is implemented in
[ci_bootstrap.py](../tools/infra/ci_bootstrap.py):

```bash
python3 tools/infra/ci_bootstrap.py paths --root .
```

Resolve any reported missing or incompatible checkout using the recorded
dependency provenance and applicable submodule configuration. A similarly
named directory is not evidence that the required package is present. Do not
run `lake update` or substitute unpinned sources as a workaround. The
[baseline audit](DOCUMENTATION_SOURCE_AUDIT_2026-11-03.md) records a CI
path-dependency failure before compilation; no successful fresh-clone result
is implied here.

Optional Arango, Hive, Pi, and Archon services are separate from these Lean
package prerequisites. Their deployment setup is described in the
[canonical pipeline](CANONICAL_AGENT_PIPELINE.md).

## 3. Choose and record the validation scope

Before compilation, inspect running processes and avoid competing compiler or
test jobs. Use the shared-lock wrappers from the checkout root:

```bash
# Build one owner and its dependencies.
python3 tools/infra/run_locked_lake_build.py \
  --wait-for-build-lock InfoGeometry.Physics.OperatorRPABlock

# Elaborate one source file using the available compiled dependencies.
python3 tools/infra/run_locked_lean.py \
  lean/InfoGeometry/Physics/OperatorRPABlock.lean

# Build changed InfoGeometry owners selected by the helper.
python3 tools/infra/run_locked_lake_build.py \
  --wait-for-build-lock --changed

# Build the main umbrella import.
python3 tools/infra/run_locked_lake_build.py \
  --wait-for-build-lock InfoGeometry.All

# Explicitly build every Lake default target.
python3 tools/infra/run_locked_lake_build.py \
  --wait-for-build-lock --all-default-targets
```

Run only the command needed for the intended check; the list is not a required
sequence. A file check does not build missing imported artifacts. A successful
changed-owner run, an umbrella build, and an all-default-target build establish
different coverage. Historical or unregistered files elsewhere in the repository
are not automatically covered by any one of these commands.

The changed-owner helper defaults to the `InfoGeometry.` module prefix,
selects supported source paths, and excludes `*.All` modules. It does not select
changed files under `proofs/` or the test directories; check those owners with
the appropriate explicit file or target command.

No-target `run_locked_lake_build.py` selects changed-owner mode. Lake options
after `--` require an explicit target or `--all-default-targets`; changed-owner
mode rejects forwarded Lake options. See the
[wrapper implementation](../tools/infra/run_locked_lake_build.py).

Never run `lake clean`, delete build caches, or share `.lake` through symlinks
between checkouts. The build helpers reject linked worktrees and symlinked
Lake roots. See the [cache policy](../WARNING_DO_NOT_RUN_CACHE.md).

## 4. Report exactly what was checked

Record the Git revision, working-tree changes, toolchain, command, target set,
exit status, and log location. Separate these evidence classes:

| Evidence | Scope |
|---|---|
| Source and signature inspection | The definitions, hypotheses, and conclusion actually written |
| Debt-marker scan | The scanned tokens in the declared source scope |
| Compilation | Elaboration of the selected sources and dependencies in that environment |
| Declaration axiom audit | Transitive axioms for the specifically audited declarations |
| Mathematical interpretation | Whether the formal statement supports the proposed comparison |

The [scope scanner](../tools/quality/repo_lean_scope_audit.py) reports package,
fixture, and other tracked sources separately. Intentional negative linter
tests must remain recognizable as fixtures. New accepted proofs must satisfy
the proof requirements in [AGENTS.md](../AGENTS.md).

## 5. Continue from the actual owner

Use the [documentation map](README.md),
[OperatorAlgebra guide](../lean/InfoGeometry/OperatorAlgebra/README.md), and
[deep-search protocol](REPO_DEEP_SEARCH_PROTOCOL.md). Read the relevant imports,
carrier definitions, theorem statements, and consumers before extending a
construction or reporting a missing bridge.
