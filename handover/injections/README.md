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
  --lane raw
```

Promote packet by id:
```bash
python3 tools/infra/injection_promote.py EXT-20260414-001 --to distilled --note "Gemini distilled"
python3 tools/infra/injection_promote.py EXT-20260414-001 --to translated --note "Codex mapped owners"
python3 tools/infra/injection_promote.py EXT-20260414-001 --to gated --note "Policy and feasibility checks passed"
python3 tools/infra/injection_promote.py EXT-20260414-001 --to accepted --note "Implemented + verified"
```

Status dashboard:
```bash
python3 tools/infra/injection_status.py
python3 tools/infra/injection_status.py --list gated
```

## Policy
- Gemini can create/distill hypotheses.
- Codex must translate + validate before any canonical edit.
- No packet reaches `accepted/` without targeted build verification.
- `artifacts/` remain generated outputs and are not committed as source of truth.
