# 66. Ideation Chunks as Generative Fuel

*Date: April 14, 2026*
*Context: Gemini-first ideation at pipeline ingress*

## Premise

A raw stream of consciousness is not noise by default.
In this repository, it is treated as pre-structured energy:

1. syntactically chunked,
2. creatively ideated,
3. evidence-verified,
4. then translated to owner symbols.

The key correction is architectural:
we do not send uncut narrative directly into theorem claims.
We first cut it into segment cards that can be routed through the existing `gemini-hermes-codex` workflow.

## Pipeline Lock

The ingress doctrine is now:

1. `raw_text` -> syntactic chunk cards (`research.segments[*].seed_text`)
2. chunk-wise creative ideation (`creative_notes`, typically Gemini)
3. chunk-wise strict evidence (`literature_evidence`, typically Hermes)
4. distilled claims + repo mapping + verification plan
5. promotion through `raw -> distilled -> translated -> gated -> accepted`

This preserves imagination without sacrificing proof hygiene.

## Why This Works

The chunk boundary is the first normalization.
It does for text what simplex normalization does for routing weights:
it prevents semantic collapse into a single uncontrolled blob.

Then the creative pass inflates representational bandwidth (new terms, links, hypotheses),
but the verification pass contracts it back to source-grounded claims.

So the pair (creative expansion, verification contraction) acts like a thermodynamic cycle for meaning:
explore, then project back to lawful structure.

## Operational Surface

The concrete ingress tool is:

- `tools/infra/injection_chunk_ideate.py`

It performs:

- syntactic chunking from packet `raw_text` (or `--text` override),
- creation/appending of `research.segments`,
- optional seeding of `creative_notes`,
- optional export of per-segment ideation prompt files,
- manifest logging under `handover/injections/manifests/`.

## Canonical Rule

Creative ideation is allowed to be high-energy.
Promotion is not.
A segment may move toward `translated` only when creative notes are paired with explicit evidence and repo mapping.

This keeps the alchemical front-end while preserving kernel-grade downstream discipline.
