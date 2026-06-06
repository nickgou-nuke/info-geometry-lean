#!/usr/bin/env bash
set -euo pipefail

ROOT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
DST_DIR="${XDG_CONFIG_HOME:-$HOME/.config}/systemd/user"
TARGET="hive-beehive.target"
DRY_RUN=0
STOP_FIRST=1

usage() {
  cat <<EOF
Usage: $(basename "$0") [--dry-run] [--keep-running]

Removes the Hive beehive systemd user units from:
  $DST_DIR

Defaults:
  - stops and disables $TARGET
  - removes all installed unit files
  - reloads the user daemon

Options:
  --dry-run       Print actions without calling systemctl or deleting files
  --keep-running  Do not stop/disable the target before removing files
EOF
}

while [[ $# -gt 0 ]]; do
  case "$1" in
    --dry-run)
      DRY_RUN=1
      ;;
    --keep-running)
      STOP_FIRST=0
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

if [[ $STOP_FIRST -eq 1 ]]; then
  if [[ $DRY_RUN -eq 1 ]]; then
    echo "Would run: systemctl --user disable --now $TARGET"
  else
    systemctl --user disable --now "$TARGET" || true
  fi
fi

for unit in "${unit_files[@]}"; do
  dst="$DST_DIR/$unit"
  if [[ $DRY_RUN -eq 1 ]]; then
    echo "Would remove: $dst"
  else
    rm -f "$dst"
    echo "Removed: $dst"
  fi
done

if [[ $DRY_RUN -eq 1 ]]; then
  echo "Would run: systemctl --user daemon-reload"
  exit 0
fi

systemctl --user daemon-reload

echo
cat <<EOF
Hive beehive systemd units removed.

If you want to start from scratch again, run:
  bash ./scripts/install_hive_beehive_systemd_units.sh
EOF
