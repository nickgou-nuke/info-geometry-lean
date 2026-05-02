#!/usr/bin/env bash
set -euo pipefail

# Prima materia chain driver
# ArXiv/BlackBook -> guarded generative burst -> socratic/invariant packet stubs

usage() {
  cat <<'USAGE'
Usage:
  tools/infra/prima_materia_chain.sh \
    --source-arxiv <path> \
    --black-book <path> \
    --topic <string> \
    [--rounds 3] [--out-root artifacts/prima_materia] [--dry-run]
USAGE
}

SOURCE_ARXIV=""
BLACK_BOOK=""
TOPIC=""
ROUNDS=3
OUT_ROOT="artifacts/prima_materia"
DRY_RUN=0

while [[ $# -gt 0 ]]; do
  case "$1" in
    --source-arxiv) SOURCE_ARXIV="$2"; shift 2 ;;
    --black-book) BLACK_BOOK="$2"; shift 2 ;;
    --topic) TOPIC="$2"; shift 2 ;;
    --rounds) ROUNDS="$2"; shift 2 ;;
    --out-root) OUT_ROOT="$2"; shift 2 ;;
    --dry-run) DRY_RUN=1; shift ;;
    -h|--help) usage; exit 0 ;;
    *) echo "Unknown arg: $1" >&2; usage >&2; exit 64 ;;
  esac
done

[[ -n "$SOURCE_ARXIV" && -n "$BLACK_BOOK" && -n "$TOPIC" ]] || {
  echo "missing required args" >&2
  usage >&2
  exit 64
}

[[ -f "$SOURCE_ARXIV" ]] || { echo "missing --source-arxiv file: $SOURCE_ARXIV" >&2; exit 66; }
[[ -f "$BLACK_BOOK" ]] || { echo "missing --black-book file: $BLACK_BOOK" >&2; exit 66; }

TS="$(date -u +%Y%m%dT%H%M%SZ)"
RUN_DIR="$OUT_ROOT/$TS"
mkdir -p "$RUN_DIR"

cat > "$RUN_DIR/context.json" <<JSON
{
  "source_arxiv": "$SOURCE_ARXIV",
  "black_book": "$BLACK_BOOK",
  "topic": "${TOPIC//"/\"}",
  "rounds": $ROUNDS,
  "created_at": "$TS"
}
JSON

GEMINI_PROMPT="$RUN_DIR/gemini_prompt.txt"
cat > "$GEMINI_PROMPT" <<EOF
You are generating prima materia for theorem-factory intake.
Topic: $TOPIC
Sources:
- ArXiv digest path: $SOURCE_ARXIV
- Black Book path: $BLACK_BOOK

Output JSON with keys:
- speculative_hypotheses: [ {title, claim, falsifier, anchor_candidates[]} ]
- socratic_repairs: [ {question, contradiction, repair} ]
- invariant_candidates: [ {name, objects, morphisms, symmetry, conserved_readout} ]
EOF

if [[ "$DRY_RUN" -eq 0 ]]; then
  tools/infra/run_gemini_guarded.sh \
    --loop-burst \
    --reason "prima materia generative burst" \
    -- gemini chat --prompt "$(cat "$GEMINI_PROMPT")" > "$RUN_DIR/gemini_output.json"
else
  cat > "$RUN_DIR/gemini_output.json" <<'JSON'
{"speculative_hypotheses":[],"socratic_repairs":[],"invariant_candidates":[]}
JSON
fi

cat > "$RUN_DIR/packet_prima_materia.json" <<JSON
{
  "schema": "hive.packet.prima_materia.v1",
  "packet_id": "prima-materia-$TS",
  "epistemic_status": "speculative",
  "topic": "${TOPIC//"/\"}",
  "source_refs": ["$SOURCE_ARXIV", "$BLACK_BOOK"],
  "artifact_ref": "$RUN_DIR/gemini_output.json"
}
JSON

cat > "$RUN_DIR/packet_socratic_stabilization.json" <<JSON
{
  "schema": "hive.packet.socratic_stabilization.v1",
  "packet_id": "socratic-$TS",
  "epistemic_status": "stabilizing",
  "falsifier": "Required in downstream normalization",
  "anchor_candidates": []
}
JSON

cat > "$RUN_DIR/packet_invariant_candidate.json" <<JSON
{
  "schema": "hive.packet.invariant_candidate.v1",
  "packet_id": "invariant-$TS",
  "epistemic_status": "corridor_ready",
  "falsifier": "Required before Lean routing",
  "anchor_candidates": []
}
JSON

echo "prima_materia_chain complete: $RUN_DIR"