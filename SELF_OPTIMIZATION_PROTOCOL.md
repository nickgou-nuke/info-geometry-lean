# Self-Optimization Protocol

This repository now has enough trusted graph and frontier tooling to support a
safe, iterative self-optimization loop.

That does not mean uncontrolled self-editing.

It means the repository can:

- inspect its own theorem topology,
- detect bridge frontiers,
- generate proposal packets,
- validate changes through Lean,
- and repeat the cycle with updated graph evidence.

## Core Rule

Use the graph as proposal guidance, not as proof authority.

The authoritative chain is:

1. trusted semantic export
2. frontier discovery
3. candidate bridge statements
4. quarantine or isolated implementation
5. Lean build validation
6. graph refresh
7. promotion or discard

## Safe Iterative Loop

1. Start from a clean branch or clone.
2. Refresh the current trusted repository state:

   ```bash
   python3 tools/update_repo_docs.py --refresh-exports
   ```

   For one isolated dry optimization cycle without any model hook yet:

   ```bash
   python3 tools/run_optimization_cycle.py
   ```

   This now defaults to a persistent reusable lab under `/tmp`, not to a fresh
   sterile worktree on every invocation.

3. Inspect the current frontier:
   - local bridge kernel: `reports/dag/skynet-v2-frontier.md`
   - downstream consumers: `reports/dag/skynet-v2-frontier-reverse.md`

4. Build a proposal packet from:
   - `skills/info-geometry-repo/references/frontier-prompt.md`
   - `skills/info-geometry-repo/references/bridge-candidates.md`

   The current runner can already materialize one tracked bridge candidate into
   the isolated quarantine module in report-only form.

5. Make the smallest useful change:
   - one bridge lemma,
   - one normalization theorem pack,
   - one export/schema improvement,
   - or one documentation/bootstrap improvement.

6. Keep generated or speculative work quarantined until validated.

   In the current dry scaffold, the quarantine target is:

   - `lean/InfoGeometry/Unstable/AutoOptCycle.lean`

   and it is created only inside the isolated worktree, not in the canonical
   working tree.

   The default worktree policy is:

   - reuse the persistent lab if it already exists
   - create the persistent lab if it does not yet exist
   - create a fresh sterile worktree only with `--fresh-worktree`
   - destroy a worktree only with explicit cleanup intent
   - hydrate the lab from the main repo's local `.lake` cache before building

7. Validate in Lean:

   ```bash
   lake build InfoGeometry.Canonical.All
   lake build -R
   ```

8. Refresh trusted graph evidence again and compare the frontier.

9. Promote the change only if:
   - the build is green,
   - the frontier is cleaner or more connected,
   - and the repository documentation still matches the actual state.

## Clone-Based Discipline

If an agent wants to explore aggressively, do it in a branch or clone, not on
the canonical surface first.

Why:

- graph-guided exploration is useful,
- but failed proposals are expected,
- and Lean validation needs a safe rollback boundary.

The current runner implements this with `git worktree`, not by switching
branches in the main working tree.

## What The Repository Can Safely Optimize

The current system is well-suited for:

- bridge discovery across trusted semantic block graphs
- theorem-normalization cleanup
- documentation refresh from current trusted artifacts
- stale-surface detection
- narrowing candidate universes for categorical tooling

It is not a license for:

- direct self-modifying proof search in canonical files
- unvalidated theorem generation
- replacing human review with graph scores

## Current Trusted Inputs

The current self-optimization loop depends on:

- `tools/semantic_block_export.py`
- `tools/skynet_v2.py`
- `tools/update_repo_docs.py`
- `docs/auto/index.md`
- `reports/dag/skynet-v2-frontier.json`
- `reports/dag/skynet-v2-frontier-reverse.json`

## Current Frontier Story

The main verified bridge is:

`InfoGeometry.KK.KasparovCycle.analyticalIndex`
-> `InfoGeometry.Canonical.AnalyticalIndex.analyticalIndex`
-> `InfoGeometry.Canonical.GrandSynthesis.*`

So the current self-optimization pressure should concentrate on:

- KK -> AnalyticalIndex bridge strengthening
- AnalyticalIndex -> GrandSynthesis consumer closure
- naturality and bridge-packet refinement around that frontier

## Generated Cycle Snapshot

The current generated cycle snapshot is written to:

- `reports/dag/self-optimization-cycle.md`

Regenerate it with:

```bash
python3 tools/generate_self_optimization_report.py
```

Run one isolated dry optimization cycle with:

```bash
python3 tools/run_optimization_cycle.py
```

Select a specific frontier row and candidate sketch with:

```bash
python3 tools/run_optimization_cycle.py \
  --frontier-index 0 \
  --candidate-index 0
```

Force a brand-new sterile worktree only when you actually want an ab initio
baseline:

```bash
python3 tools/run_optimization_cycle.py \
  --fresh-worktree \
  --frontier-index 0 \
  --candidate-index 0
```
