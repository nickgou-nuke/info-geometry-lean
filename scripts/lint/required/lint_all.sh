#!/usr/bin/env bash
set -euo pipefail
ROOT="$(cd "$(dirname "${BASH_SOURCE[0]}")/../../.." && pwd)"
cd "$ROOT"
LEAN_SOURCE_ROOT="${LEAN_SOURCE_ROOT:-$(if [[ -d src ]]; then printf src; else printf lean; fi)}"
skip_build=false
all=false
files=()
for arg in "$@"; do
  case "$arg" in
    --skip-build) skip_build=true ;;
    --all) all=true ;;
    --*) echo "unknown option: $arg" >&2; exit 2 ;;
    *) files+=("$arg") ;;
  esac
done
scope=()
[[ "$all" == true ]] && scope+=(--all)
[[ ${#files[@]} -gt 0 ]] && scope+=("${files[@]}")
theorem_scope=()
if [[ "$all" == true ]]; then
  theorem_scope+=("$LEAN_SOURCE_ROOT")
elif [[ ${#files[@]} -gt 0 ]]; then
  theorem_scope+=("${files[@]}")
else
  mapfile -t theorem_scope < <(git diff --name-only --diff-filter=ACMRTUXB HEAD -- lean src | while IFS= read -r path; do [[ "$path" == *.lean && -f "$path" ]] && printf '%s\n' "$path"; done)
fi
step() { echo "[lint-all] $1"; shift; "$@"; }
step "1/8 Lean style" python3 scripts/lint/required/style_lint.py "${scope[@]}"
if [[ "$skip_build" == false ]]; then
  step "2/8 locked Lake build" python3 tools/infra/run_locked_lake_build.py --wait-for-build-lock
else
  echo "[lint-all] 2/8 locked Lake build (skipped by --skip-build)"
fi
step "3/8 import completeness" python3 scripts/lint/required/import_completeness.py "${scope[@]}"
step "4/8 duplicate TODO comments" python3 scripts/lint/required/todo_dedup.py "${scope[@]}"
step "5/8 @[pseudo] attribution" python3 scripts/lint/required/pseudo_attribution.py "${scope[@]}"
step "6/8 module documentation" python3 scripts/lint/required/module_doc_lint.py "${scope[@]}"
step "7/8 theorem declarations, docstrings, and Lean linters" python3 scripts/lint/required/theorem_lint.py "${theorem_scope[@]}"
step "7/8 no-hypothesis mandate" python3 tools/quality/check_no_hypothesis_mandate.py
step "8/8 transitive import closure" python3 scripts/lint/required/transitive_import_lint.py "${scope[@]}"
step "9/9 repository structural linter" python3 scripts/lint/required/repo_structure_lint.py
