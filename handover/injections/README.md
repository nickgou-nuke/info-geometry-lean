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
- For `research.workflow.mode=gemini-hermes-codex`, promotion to `translated` requires:
  - `creative_complete=true`
  - `verification_complete=true`
  - non-empty segment cards with `creative_notes` and `literature_evidence`.
