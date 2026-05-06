#!/usr/bin/env bash
set -euo pipefail

ROOT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
SERVICE_SRC="$ROOT_DIR/systemd/system/leanstral-gguf-llama.service"
SERVICE_DST="/etc/systemd/system/leanstral-gguf-llama.service"

sudo systemctl disable --now qwen36-vllm.service 2>/dev/null || true
sudo install -m 0644 "$SERVICE_SRC" "$SERVICE_DST"
sudo systemctl daemon-reload
sudo systemctl enable leanstral-gguf-llama.service

cat <<EOF
Installed and enabled leanstral-gguf-llama.service.

Start now:
  sudo systemctl start leanstral-gguf-llama.service

Inspect:
  systemctl status leanstral-gguf-llama.service --no-pager
  journalctl -u leanstral-gguf-llama.service -f

Check endpoint after startup:
  lake script run checkResidentModel --base-url http://127.0.0.1:18789/v1 --expected-model leanstral-gguf --probe-chat
EOF
