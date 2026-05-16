#!/usr/bin/env bash
set -euo pipefail

ROOT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
SRC_DIR="$ROOT_DIR/systemd/user"
DST_DIR="${XDG_CONFIG_HOME:-$HOME/.config}/systemd/user"
TARGET="hive-beehive.target"
START_AFTER_ENABLE=1
DRY_RUN=0

usage() {
  cat <<EOF
Usage: $(basename "$0") [--no-start] [--dry-run]

Installs the Hive beehive systemd user units into:
  $DST_DIR

Defaults:
  - copies all unit files from $SRC_DIR
  - reloads the user daemon
  - enables and starts $TARGET

Options:
  --no-start   Install and enable, but do not start the target
  --dry-run    Print actions without copying or calling systemctl
EOF
}

while [[ $# -gt 0 ]]; do
  case "$1" in
    --no-start)
      START_AFTER_ENABLE=0
      ;;
    --dry-run)
      DRY_RUN=1
      ;;
    -h|--help)
      usage
      exit 0
      ;;
    *)
      echo "Unknown argument: $1" >&2
      usage >&2
      exit 2
      ;;
  esac
  shift
done

unit_files=(
  hive-beehive.target
  hive-motherbee.service
  hive-bee@.service
  hive-swarm@.service
  hive-build@.service
  hive-audit@.service
  hive-research@.service
)

if [[ ! -d "$SRC_DIR" ]]; then
  echo "Missing source directory: $SRC_DIR" >&2
  exit 2
fi

mkdir -p "$DST_DIR"

for unit in "${unit_files[@]}"; do
  src="$SRC_DIR/$unit"
  dst="$DST_DIR/$unit"
  if [[ ! -f "$src" ]]; then
    echo "Missing unit file: $src" >&2
    exit 2
  fi
  if [[ $DRY_RUN -eq 1 ]]; then
    echo "Would install: $src -> $dst"
  else
    install -m 0644 "$src" "$dst"
    echo "Installed: $dst"
  fi
done

if [[ $DRY_RUN -eq 1 ]]; then
  echo "Would run: systemctl --user daemon-reload"
  if [[ $START_AFTER_ENABLE -eq 1 ]]; then
    echo "Would run: systemctl --user enable --now $TARGET"
  else
    echo "Would run: systemctl --user enable $TARGET"
  fi
  exit 0
fi

systemctl --user daemon-reload
systemctl --user enable "$TARGET"
if [[ $START_AFTER_ENABLE -eq 1 ]]; then
  systemctl --user start "$TARGET"
fi

echo
if [[ $START_AFTER_ENABLE -eq 1 ]]; then
  echo "Hive beehive systemd units installed, enabled, and started."
else
  echo "Hive beehive systemd units installed and enabled."
fi

echo
cat <<EOF
Useful status commands:
  systemctl --user status $TARGET
  systemctl --user status hive-motherbee.service
  systemctl --user status hive-bee@default.service
  systemctl --user status hive-swarm@default.service
  systemctl --user status hive-build@default.service
  systemctl --user status hive-audit@default.service
  systemctl --user status hive-research@default.service

Useful log commands:
  journalctl --user -u $TARGET -f
  journalctl --user -u hive-motherbee.service -f
EOF
