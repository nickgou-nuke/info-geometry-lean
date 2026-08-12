#!/usr/bin/env bash
set -euo pipefail

ROOT_DIR="$(cd "$(dirname "$0")/.." && pwd)"
cd "$ROOT_DIR"

MANIFEST="scripts/quality/quarantine_manifest.txt"

declare -a QUARANTINED_MODULES=()
declare -A QUARANTINED_FILES=()

while IFS='|' read -r raw_module _; do
  module="$(echo "${raw_module}" | xargs)"
  [[ -z "$module" || "$module" == \#* ]] && continue
  QUARANTINED_MODULES+=("$module")
  module_path="lean/${module//./\/}.lean"
  if [[ -f "$module_path" ]]; then
    QUARANTINED_FILES["$module_path"]=1
  fi
done < "$MANIFEST"

is_allowed_importer() {
  local file="$1"
  if [[ "$file" == lean/InfoGeometry/Unstable/* ]]; then
    return 0
  fi
  [[ -n "${QUARANTINED_FILES[$file]:-}" ]]
}

status=0

for module in "${QUARANTINED_MODULES[@]}"; do
  escaped_module="${module//./\\.}"
  while IFS=: read -r file line _; do
    [[ -z "$file" ]] && continue
    if ! is_allowed_importer "$file"; then
      echo "Forbidden quarantined import: $module in $file:$line"
      status=1
    fi
  done < <(
    rg -n "^[[:space:]]*import[[:space:]]+${escaped_module}(\\b|$)" \
      lean \
      --no-heading || true
  )
done

if [[ "$status" -ne 0 ]]; then
  echo "Quarantine import boundary check failed."
  exit 1
fi

echo "Quarantine import boundary check passed."
