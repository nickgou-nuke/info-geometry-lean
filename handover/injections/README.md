# Knowledge Injection Subsystem

This subsystem keeps the repo open to external input while preserving owner discipline.

## Lanes
- `raw/`: direct intake from web/chats/manual streams.
- `distilled/`: Gemini-side synthesis into candidate claim packets.
- `translated/`: Codex-side mapping into repo-native owners/symbols.
- `gated/`: packets that passed provenance + feasibility checks and are ready to implement.
- `accepted/`: integrated and validated packets.
- `rejected/`: packets blocked by policy (with reason in history note).
- `archive/`: closed historical packets.

## Packet Contract
Schema: `handover/injections/schema/claim_packet.schema.json`

Infra runtime dependency:
```bash
.venv/bin/pip install "jsonschema==4.23.0"
```

Every packet must have:
- stable `packet_id`
- provenance (`source.type`, `source.ref`, `source.date`)
- `distilled_claim`
- `repo_mapping` (owner files/symbols/theorem targets)
- `verification_plan` (targeted build surface)
- `status`
- `history` trail

## CLI Commands
Create a packet in `raw/`:
```bash
python3 tools/infra/injection_create_packet.py \
  --source-type manual \
  --source-ref "chat-2026-04-14" \
  --title "CP-BOOT external stream" \
  --authority-tier repo_native \
  --raw-text "Initial external vision input"
```

Create a topic-focused deep-research packet:
```bash
python3 tools/infra/injection_research_packet.py \
  --topic "Your specific research topic" \
  --question "Question 1" \
  --question "Question 2" \
  --source-url "https://..." \
  --source-paper "arXiv:..." \
  --authority-tier external_analogy \
  --workflow-mode gemini-hermes-codex \
  --segment "segment seed text #1" \
  --segment "segment seed text #2" \
  --lane raw
```

Attach Gemini/Hermes segment enrichment:
```bash
python3 tools/infra/injection_enrich_segment.py <PACKET_ID> \
  --segment-id S1 \
  --creative-notes "Gemini concept expansion..." \
  --claim "Claim A" \
  --inference-flag "inference:analogy" \
  --evidence-url "https://..." \
  --evidence-summary "Hermes-verified source summary..." \
  --mark-creative-complete

python3 tools/infra/injection_enrich_segment.py <PACKET_ID> \
  --segment-id S1 \
  --enriched-context "Hermes deep search synthesis..." \
  --evidence-url "https://..." \
  --evidence-summary "Second evidence summary..." \
  --mark-verification-complete
```

Run OpenAI Deep Research via MCP gateway and ingest result:
```bash
# Terminal A: run the gateway
python3 tools/infra/openai_deep_research_gateway.py

# Then from your MCP client call:
# 1) dr_start(...)
# 2) dr_status(response_id) until status=completed
# 3) dr_ingest_result_to_packet(response_id=<id>, packet=<PACKET_ID>, segment_id=S1)
```

Promote packet by id:
```bash
python3 tools/infra/injection_promote.py EXT-20260414-001 --to distilled --note "Gemini distilled"
python3 tools/infra/injection_promote.py EXT-20260414-001 --to translated --note "Codex mapped owners"
python3 tools/infra/injection_promote.py EXT-20260414-001 --to gated --note "Policy and feasibility checks passed"
python3 tools/infra/injection_promote.py EXT-20260414-001 --to accepted --note "Implemented + verified"
```

Build SLO report and optional alert gates:
```bash
python3 tools/infra/injection_slo_report.py
python3 tools/infra/injection_slo_report.py \
  --max-failure-rate 0.10 \
  --max-p95-latency-sec 7200 \
  --max-p95-lock-wait-sec 1.0 \
  --min-gpu-free-mb 1024
```

Status dashboard:
```bash
python3 tools/infra/injection_status.py
python3 tools/infra/injection_status.py --list gated
```

Build reviewer-ready digest from a packet:
```bash
python3 tools/infra/injection_build_digest.py <PACKET_ID> --update-packet
```

## Policy
- Gemini can create/distill hypotheses.
- Gemini can run creative segment expansion before verification.
- Hermes should perform strict evidence enrichment before translation.
- Codex must translate + validate before any canonical edit.
- No packet reaches `accepted/` without targeted build verification.
- `artifacts/` remain generated outputs and are not committed as source of truth.
- Every mutation path (`create/research/promote/build_digest --update-packet`) is schema-validated.
- Every mutation path uses per-packet file locks and atomic writes.
- Promotion uses a strict transition graph (no skip overrides).
- `authority_tier` controls promotion discipline:
  - `repo_native`: full lane promotion allowed (subject to existing gates).
  - `external_analogy`: may translate to owner mappings, but automation blocks promotion to `gated/accepted`.
- For `research.workflow.mode=gemini-hermes-codex`, promotion to `translated` requires:
  - `creative_complete=true`
  - `verification_complete=true`
  - non-empty segment cards with `creative_notes` and `literature_evidence`.

## Current Codebase Status

Status pointer refreshed: 2026-04-16 (Europe/Sofia). See [../../docs/CODEBASE_STATUS.md](../../docs/CODEBASE_STATUS.md) for the current build/audit state.

