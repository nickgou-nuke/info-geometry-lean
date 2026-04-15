# OpenAI Deep Research Brief Template

Use this when calling `dr_start` in the OpenAI Deep Research gateway.

## Brief

Research topic: `<TOPIC>`

Goal:
- establish current repository implementation status (`implemented/interface/missing/docs-only/speculative`)
- extract owner-surface anchors (files + declaration names)
- separate proved facts vs analogies vs speculative hypotheses

Scope:
- `lean/InfoGeometry`
- `docs/black_books`
- `docs`
- `handover/injections`
- `tools/infra`

Deliverables:
1. coverage matrix with status labels
2. context pack for coding agents and Socratic dialogue
3. explicit unresolved gaps and next owner surfaces

Citation policy:
- provide URL + title + date when possible
- label inferences explicitly
- avoid unsupported theorem claims

## Instructions

- prioritize primary sources and official documentation
- include contradictory evidence if found
- keep claims falsifiable and implementation-oriented
- output concise sections with headings
