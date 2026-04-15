# Deep Research Ingest Skill

## Purpose
Run topic-focused deep research using internet + literature sources and inject results into the repo's authoritative intake pipeline (`handover/injections/*`).

This skill is for:
- specific-topic web and paper discovery
- source-quality triage
- structured distillation into claim packets
- translation-ready handoff for codex execution lane

## Core Rules
- Prefer primary sources: official docs, papers, standards, maintainers.
- Preserve provenance for every claim (URL, title, date).
- Keep research and implementation separate:
  - Gemini lane: exploration/distillation
  - Codex lane: translation/validation/integration
- No direct canonical edits from raw research text.

## Output Contract
Every research session must produce a packet in `handover/injections/` with:
- `packet_id`, `title`, `source`
- `raw_text` (topic + raw findings)
- `research` block with questions and sources
- `distilled_claim` (if available)
- `repo_mapping` placeholders (or concrete mapping when translated)
- `verification_plan` placeholders (or concrete build targets)

## Workflow
1. Define topic and questions.
2. Syntactic chunk pass: cut intake into segment cards.
3. Gemini pass: creative elaboration per chunk.
4. Hermes pass: strict literature/evidence enrichment per segment.
5. Seed/update packet in `raw`/`distilled` with workflow and segment cards.
6. Promote through lanes as certainty increases.
7. Translate to repo-native owner surfaces before coding.

## Commands
Seed a research packet:
```bash
python3 tools/infra/injection_research_packet.py \
  --topic "Tomita-Takesaki modular flow on doubled-real carrier" \
  --question "What bounded surrogate theorem family is feasible now?" \
  --question "What owner files already prove prerequisites?" \
  --source-url "https://example.org/paper" \
  --source-url "https://example.org/docs" \
  --workflow-mode gemini-hermes-codex \
  --segment "seed segment one" \
  --segment "seed segment two" \
  --lane raw
```

Syntactic chunking + ideation prompt export:
```bash
python3 tools/infra/injection_chunk_ideate.py <PACKET_ID> \
  --max-chars 650 \
  --prompt-dir handover/injections/prompts/<PACKET_ID> \
  --set-workflow-mode gemini-hermes-codex
```

Gemini CLI account-auth capture (no API key):
```bash
python3 tools/infra/injection_capture_gemini_cli.py <PACKET_ID> \
  --gemini-bin gemini \
  --input-mode stdin \
  --sleep-sec 4 \
  --mark-creative-complete
```

Single-segment account-auth adapter (Hermes piping mode):
```bash
echo '{"segment_id":"S1","content":"..."}' \
  | python3 tools/infra/gemini_account_adapter.py \
      --gemini-bin gemini \
      --input-mode stdin
```

Attach segment enrichment from Gemini/Hermes:
```bash
python3 tools/infra/injection_enrich_segment.py <PACKET_ID> \
  --segment-id S1 \
  --creative-notes "Gemini creative expansion..." \
  --claim "candidate claim" \
  --inference-flag "inference:creative" \
  --mark-creative-complete

python3 tools/infra/injection_enrich_segment.py <PACKET_ID> \
  --segment-id S1 \
  --enriched-context "Hermes verified context..." \
  --evidence-url "https://example.org/source" \
  --evidence-summary "evidence summary" \
  --mark-verification-complete
```

Promote packet:
```bash
python3 tools/infra/injection_promote.py <PACKET_ID> --to distilled --note "distilled"
python3 tools/infra/injection_promote.py <PACKET_ID> --to translated --note "repo-mapped"
python3 tools/infra/injection_promote.py <PACKET_ID> --to gated --note "ready to implement"
```

Status:
```bash
python3 tools/infra/injection_status.py --list raw
python3 tools/infra/injection_status.py --list distilled
```

Build reviewer/examiner digest:
```bash
python3 tools/infra/injection_build_digest.py <PACKET_ID> --update-packet
```

OpenAI Deep Research gateway (Codex-facing MCP):
```bash
python3 tools/infra/openai_deep_research_gateway.py
```

Then from MCP client tooling:
- `dr_start` with deep-research brief and source config
- `dr_status` until `completed`
- `dr_ingest_result_to_packet` to attach output into packet segment cards

## Quality Checklist
- Source dates verified
- Contradictions noted
- Inference labeled as inference
- For `gemini-hermes-codex` mode, both workflow stage flags are set to true before `translated`
- No speculative theorem names without owner symbols
- Targeted verification surface identified before integration
