# Markdown Corpus Governance

Last updated: 2026-04-18 (Europe/Sofia)

This document defines how we keep the markdown corpus readable and non-confusing
without touching Black Books chapter content.

## Scope And Exclusions

The markdown hygiene pass covers all tracked `*.md` files and explicitly excludes:

- `docs/black_books/`
- `docs/black_books_refactor/`

Black Books remain protected exploration material and are not rewritten by the
cleanup lane.

## Automated Classification And Hygiene

Run classification first, then hygiene.

### Baseline pass (default)

```bash
python3 tools/infra/reports/classify_markdown_corpus.py \
  --json-out reports/dag/markdown-classification.json \
  --md-out reports/dag/markdown-classification.md

python3 tools/infra/reports/generate_markdown_hygiene_report.py \
  --classification-json reports/dag/markdown-classification.json \
  --json-out reports/dag/markdown-hygiene.json \
  --md-out reports/dag/markdown-hygiene.md
```

### Strict cleanup pass (for stale/confusing docs)

Use this when cleaning scattered README and orphan-note surfaces:

```bash
python3 tools/infra/reports/generate_markdown_hygiene_report.py \
  --classification-json reports/dag/markdown-classification.json \
  --json-out reports/dag/markdown-hygiene.json \
  --md-out reports/dag/markdown-hygiene.md \
  --stale-days 45 \
  --hard-stale-days 120 \
  --low-confidence-threshold 0.55 \
  --min-word-thin 120
```

Latest strict pass snapshot (2026-04-18):

- reviewed files: `481`
- excluded files: `155` (Black Books corridors)
- `review_update` candidates: `24`
- `review_or_archive` candidates: `0`

Current action states from hygiene are:

- `keep`: content is usable as-is.
- `review_update`: update wording/links/status header.
- `review_or_archive`: archive or remove from active navigation.
- `protected_keep`: do not demote from canonical entry surface.

## Canonical Entry Surface

When docs disagree, trust Lean source and maintained operator docs in this order:

1. `README.md`
2. `docs/README.md`
3. `docs/OperatorQuickstart.md`
4. `docs/LOCAL_TOOLCHAIN_ARCHITECTURE.md`
5. `docs/ToolingMethodology.md`
6. `tools/infra/README.md`
7. `docs/RepositoryMemoryMap.md`

## README Consolidation Queue (Non-Black-Book)

These README files are useful but should be treated as local context surfaces,
not global authority:

- [`.agents/workflows/repo-topic-deep-research/README.md`](../.agents/workflows/repo-topic-deep-research/README.md)
- [`leantrail/ui/README.md`](../leantrail/ui/README.md)
- [`archive/README.md`](../archive/README.md)
- [`archive/legacy/scripts/README.md`](../archive/legacy/scripts/README.md)
- [`artifacts/dag/README.md`](../artifacts/dag/README.md)
- [`blueprint/README.md`](../blueprint/README.md)
- [`external_refs/llama4/README.md`](../external_refs/llama4/README.md)
- [`external_refs/mcbal_blog/library/README.md`](../external_refs/mcbal_blog/library/README.md)
- [`handover/agentic_autotheory_2026-04-15/README.md`](../handover/agentic_autotheory_2026-04-15/README.md)
- [`handover/injections/README.md`](../handover/injections/README.md)
- [`tools/infra/autonomous_math/README.md`](../tools/infra/autonomous_math/README.md)
- [`skills/README.md`](../skills/README.md)

## Update Rules

1. Keep a short `Status` block at the top of local README files.
2. Add at least one inbound link from canonical docs for every retained README.
3. Archive or merge files marked `review_or_archive` for two consecutive strict hygiene runs.
4. Do not hand-edit generated report surfaces under `reports/` unless repairing generators.
5. Re-run classification+hygiene after every documentation cleanup packet.
6. Prefer markdown filenames without spaces/parentheses to keep link resolution deterministic.
7. Treat `review_update` + `orphan` docs as the active backlog for link consolidation into canonical entry surfaces.
