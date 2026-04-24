#!/usr/bin/env bash
set -euo pipefail

# Usage:
#   templates/run_chatgpt_import.sh /abs/path/to/conversations.json [/abs/path/to/repo-with-agentic-stack]

INPUT_JSON="${1:-}"
TARGET_REPO="${2:-}"
OUT_DIR="${HOME}/.hermes/imports/chatgpt"
SCRIPT_PATH="${HOME}/.hermes/skills/autonomous-ai-agents/chatgpt-history-to-hermes/scripts/chatgpt_history_migrate.py"

if [[ -z "${INPUT_JSON}" ]]; then
  echo "ERROR: pass path to conversations.json"
  exit 2
fi

python3 "${SCRIPT_PATH}" --input "${INPUT_JSON}" --out "${OUT_DIR}"

echo "\nArtifacts generated under: ${OUT_DIR}"

if [[ -n "${TARGET_REPO}" && -d "${TARGET_REPO}/.agent" ]]; then
  mkdir -p "${TARGET_REPO}/.agent/memory/episodic/chatgpt-import"
  mkdir -p "${TARGET_REPO}/.agent/memory/semantic/chatgpt-import"

  cp "${OUT_DIR}"/sessions_md/*.md "${TARGET_REPO}/.agent/memory/episodic/chatgpt-import/" || true
  cp "${OUT_DIR}/normalized_conversations.jsonl" "${TARGET_REPO}/.agent/memory/semantic/chatgpt-import/"
  cp "${OUT_DIR}/memory_candidates.jsonl" "${TARGET_REPO}/.agent/memory/semantic/chatgpt-import/"

  echo "Agentic-stack wiring complete under ${TARGET_REPO}/.agent/memory"
fi

echo "Done. Next: review ${OUT_DIR}/memory_candidates.jsonl and ingest durable facts into Hermes memory."
