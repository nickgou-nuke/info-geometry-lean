# How Deep Research works and how to program it for agentic flow

## Executive summary

Deep Research is two different things depending on surface:

1. ChatGPT product behavior: user-facing planning, clarification, progress tracking, and cited reports.
2. API behavior: model + tools surface where the developer must implement most orchestration logic.

For this repository, the safe implementation rule is:

`clarify -> rewrite -> plan -> retrieve -> verify -> synthesize -> gate -> handoff`

The model does not own closure. The Lean kernel and ClawCode gates own closure.

## Product surface vs API surface

The product flow includes front-end orchestration that the raw API does not guarantee.
If we want reproducible agentic behavior in repo workflows, we must explicitly implement:

- clarification stage (resolve ambiguity early),
- brief rewrite stage (turn user ask into executable research contract),
- controlled retrieval stage (tool/source bounded),
- verifier stage (coverage and contradiction checks),
- synthesis stage (report from evidence),
- gate stage (packet validity, provenance, closure policy).

This is why "Deep Research as a single call" is not enough for repository-grade operation.

## Repo-native architecture

The runtime authority order remains:

1. Hermes intake/discovery in quarantine,
2. OpenClaw expansion and bridge drafting,
3. NemoClaw architectural placement and lane legality,
4. DocClaw compression after stabilization,
5. ClawCode + Lean compiler for closure.

Deep research is therefore a front-end cognition lane, not a sovereign planner.

## Implementation contract

The controller contract is now:

1. `clarifier.py` produces a typed clarification object:
   - `needs_clarification`
   - `clarifying_questions`
   - `assumptions`
   - `clarified_goal`
2. `brief_rewriter.py` produces a typed execution brief:
   - `research_brief`
   - `scope`
   - `exclusions`
   - `source_preferences`
   - `desired_output`
   - `evaluation_criteria`
3. `planner.py` turns the brief into subquestions.
4. `retriever.py` executes bounded evidence collection over allowed tools.
5. `verifier.py` checks coverage and unresolved conflicts.
6. `writer.py` synthesizes final report only if hard gates pass.
7. `research_packet.py` builds the typed Hermes handoff packet.
8. `check_research_handoff_gate.py` enforces packet + provenance requirements before closure routing.

## Programming pattern

Use staged controllers:

- `tools/infra/deep_research/controller.py`
- `tools/infra/autonomous_math/research_controller.py`

Both now support:

- `--clarifier-model`
- `--rewriter-model`
- `--skip-clarify`
- `--skip-rewrite`

Both persist:

- original goal,
- clarified goal,
- execution brief,
- execution constraints,
- plan/findings/verification,
- gate status and activity trace.

## Safety and legality guardrails

Three hard rules:

1. No theorem or closure proposal may originate from uncited prose alone.
2. No final report without coverage and citation gates.
3. No closure promotion without typed packet + NemoClaw provenance + ClawCode gate.

This keeps Jungian exploration available while preserving Pauli closure discipline.

## Minimal operator runbook

Deep research staged run:

```bash
python3 tools/infra/deep_research/controller.py \
  --goal "Assess implementation options for X" \
  --allowed-sources web,files \
  --trusted-domain openai.com \
  --trusted-domain platform.openai.com
```

Autonomous math run:

```bash
python3 tools/infra/autonomous_math/research_controller.py \
  --goal "Formalize support-restricted modular Hamiltonian on Preg" \
  --allowed-sources web
```

Gate check:

```bash
python3 tools/infra/research_packet.py validate --packet <packet.json>
python3 tools/infra/check_research_handoff_gate.py \
  --packet <packet.json> \
  --nemoclaw-note <note.md>
```

## Final repository doctrine

Deep research generates evidence and structure.
It does not generate truth by itself.

Truth remains:

- Lean source,
- architecture audit,
- closure gates,
- kernel-checked theorems.
