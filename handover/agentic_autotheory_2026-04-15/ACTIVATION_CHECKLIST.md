# Activation Checklist (2026-04-15)

## Day-0 Activation

1. Confirm canonical files are present:
   - `tools/prompts/agentic_handover_policy_2026-04-15.md`
   - `tools/prompts/agentic_autotheory_prompts_2026-04-15.md`
   - `tools/prompts/agentic_personas_2026-04-15.md`
2. Route agents:
   - `NemoClaw` -> Prompt A (architect emphasis)
   - `OpenClaw` -> Prompt A (creator emphasis)
   - `ClawCode` -> Prompt B (caretaker gatekeeper)
3. Enforce lane model:
   - Lane A: raw intake
   - Lane B: stabilization
   - Lane C: authoritative

## Authoritative Gate Sequence

Run in order:

1. `lake build InfoGeometry.All`
2. `python3 tools/infra/dag_refresh.py`
3. `python3 tools/infra/dag_reports.py`
4. `python3 tools/infra/dag_doctor.py`

Admission condition:

- `dag_doctor` must report `fail=0`.

## Failure Handling

If any gate fails:

1. classify failure:
   - source defect
   - policy mismatch
   - stale artifacts
   - quarantine omission
2. patch minimal corrective surface
3. rerun affected gate(s)
4. rerun full gate sequence

## Daily Handoff Record

Each cycle must emit:

1. Architect note (ownership/adjacency decisions)
2. Creator note (patch + assumptions)
3. Caretaker note (gate outcomes + admit/block decision)

