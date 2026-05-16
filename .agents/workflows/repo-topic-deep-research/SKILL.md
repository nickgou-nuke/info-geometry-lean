---
name: repo-topic-deep-research
description: Use when you need a deep, topic-focused investigation of repository coverage and maturity (implemented/interface/missing), plus a formalized context pack for LLM/agent reasoning and Socratic dialogue.
---

## Constructive Closure Mandate

Replacing witness-gated and external-certificate leftovers with native Lean 4 proofs is the highest mandate. Treat witness packets, certificate fields, external certificates, assumption interfaces, literature owners, graph edges, and physics analogies as closure debt until discharged by kernel-checked Lean or imported mathlib theorems. Follow docs/CONSTRUCTIVE_CLOSURE_MANDATE.md; never promote anonymous or unformalized sockets as complete.

# Repo Topic Deep Research

Use this skill to investigate any topic in this repo (replace `einstein` with your target token set), then produce:

1. a reproducible coverage audit
2. a strict implementation-status matrix
3. a formalized context pack for downstream coding agents and Socratic dialogue

This skill is intentionally topic-agnostic.

## Inputs

Set these first:

- `TOPIC`: primary keyword (for example: `einstein`, `kramers`, `triality`, `router`)
- `ALIASES`: topic synonyms and adjacent terms
- `SCOPE`: default `lean/InfoGeometry docs/black_books docs reports`
- `OUTPUT_STEM`: kebab-case stem for outputs (for example: `einstein`, `triality-router`)

## Status Labels (mandatory)

Every concept row must be labeled with exactly one:

- `implemented`: theorem-bearing owner surface exists now
- `interface`: compiled skeleton/bridge, explicitly partial
- `missing`: no owner theorem surface found
- `docs-only`: present only in docs/black-books, not Lean owner code
- `speculative`: present as hypotheses/unproven registry claims

## Hard Rules

- Do not claim "exhaustive" without unbounded scan evidence (`rg --stats`).
- Separate textual mentions from semantic declarations.
- Prefer owner files over wrappers/umbrellas.
- Detect proof debt with bounded regex (`\\bsorry\\b`, declaration-level `axiom`).
- Mark inference as inference.

## Workflow

### 1) Unbounded recall scan

Run full-text scans with stats and machine-readable output:

```bash
TOPIC="einstein"
OUT="reports/${TOPIC}.matches.jsonl"

rg -i --stats --glob='*.lean' --glob='*.md' "${TOPIC}" lean/InfoGeometry docs/black_books docs reports
rg -i --json --glob='*.lean' --glob='*.md' "${TOPIC}" lean/InfoGeometry docs/black_books docs reports > "${OUT}"
```

Then scan aliases similarly and merge findings.

### 2) Candidate declaration extraction

Collect declaration candidates from Lean files:

```bash
rg -n --glob='*.lean' "theorem|lemma|def|structure|inductive|class" lean/InfoGeometry \
  | rg -i "${TOPIC}|ALIAS1|ALIAS2"
```

### 3) Owner-surface verification

- Open candidate files directly.
- Verify whether declarations are theorem-bearing or only packaging wrappers.
- Record concrete anchors (file + declaration names).

### 4) Debt/vacuity pass

For topic-matched Lean files:

```bash
FILES=$(rg -l -i --glob='*.lean' "${TOPIC}|ALIAS1|ALIAS2" lean/InfoGeometry)
rg -n "\\bsorry\\b|^[[:space:]]*axiom\\b|^[[:space:]]*constant\\b" $FILES
```

### 5) Semantic expansion (Lean-aware)

Use Lean queries for non-token semantic neighbors:

- `#print prefix <Namespace>`
- `#find ...` (type-pattern search)
- `#print axioms <decl>` for capstones/critical declarations

### 6) Classify and write matrix

Produce one matrix row per concept with:

- concept name
- status label
- owner anchors
- short note explaining classification

### 7) Build context pack for agents

Generate a topic context pack containing:

- terminology map (canonical symbols + aliases)
- proved core and boundaries
- open gaps and suggested next owner surfaces
- Socratic prompts (challenge questions with expected evidence type)

## Output Contract

Create these artifacts per run:

- `reports/<OUTPUT_STEM>.matches.jsonl`
- `reports/<OUTPUT_STEM>.scan_stats.md`
- `docs/<OUTPUT_STEM>_coverage_matrix.md`
- `docs/<OUTPUT_STEM>_context_pack.md`

Optional:

- `reports/<OUTPUT_STEM>.decl_candidates.tsv`
- `reports/<OUTPUT_STEM>.axiom_audit.md`

## Suggested Output Structure

Use the templates in:

- `skills/repo-topic-deep-research/templates/coverage_matrix_template.md`
- `skills/repo-topic-deep-research/templates/context_pack_template.md`
- `skills/repo-topic-deep-research/templates/gemini_cli_prompt_template.md`
- `skills/repo-topic-deep-research/templates/hermes_enrichment_prompt_template.md`
- `skills/repo-topic-deep-research/templates/openai_deep_research_brief_template.md`
- `skills/repo-topic-deep-research/templates/topic_dossier_template.md`
- `skills/repo-topic-deep-research/templates/lean_context_pack_template.lean`
- `skills/repo-topic-deep-research/templates/architecture_snapshot_template.md`

## Lane Mirrors

- Copilot workflow mirror:
  - `.agents/workflows/repo-topic-deep-research/SKILL.md`
  - `.agents/workflows/repo-topic-deep-research/templates/*`
- Gemini CLI creative lane:
  - `skills/repo-topic-deep-research/templates/gemini_cli_prompt_template.md`
- Hermes verification lane:
  - `skills/repo-topic-deep-research/templates/hermes_enrichment_prompt_template.md`
- OpenAI Deep Research lane:
  - `tools/infra/openai_deep_research_gateway.py`
  - `skills/repo-topic-deep-research/templates/openai_deep_research_brief_template.md`

## Quality Checklist

- Stats-backed recall evidence captured
- Every matrix row has a status label
- Every `implemented/interface/missing` claim has file anchors
- Docs-only/speculative content clearly separated from Lean owner code
- Axiom/debt checks run on topic-matched Lean files
- Context pack includes explicit boundaries and open questions
