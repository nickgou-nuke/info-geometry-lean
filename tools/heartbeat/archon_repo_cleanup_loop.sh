#!/usr/bin/env bash
set -euo pipefail

ROOT="${ROOT:-/home/goutev/repos/info-geometry-lean}"
SCOPE="${SCOPE:-lean}"
WORKFLOW="${WORKFLOW:-proof-purification-pipeline}"
# Defaults are intentionally unbounded: this is a living cleanup heartbeat.
# Stop it with Ctrl-C. Set MAX_ITERATIONS>0, MAX_STALE_ITERATIONS>0,
# STOP_WHEN_CLEAN=1, or ARCHON_CYCLE_TIMEOUT_SECONDS>0 only when a bounded
# batch run is explicitly desired.
MAX_ITERATIONS="${MAX_ITERATIONS:-0}"
MAX_STALE_ITERATIONS="${MAX_STALE_ITERATIONS:-0}"
STOP_WHEN_CLEAN="${STOP_WHEN_CLEAN:-0}"
ARCHON_CYCLE_TIMEOUT_SECONDS="${ARCHON_CYCLE_TIMEOUT_SECONDS:-0}"
# Optional breathing room between ticks. Default 0 preserves the life-force loop.
INTERVAL_SECONDS="${INTERVAL_SECONDS:-0}"
# Optional deterministic command run after each iteration for mathlib/full-repo gates.
# Example: POST_TICK_COMMAND='lake build -R'
POST_TICK_COMMAND="${POST_TICK_COMMAND:-}"
# Deterministic diff gate: rejects newly introduced proof-proxy structures/fields.
PROOF_PROXY_DIFF_GATE="${PROOF_PROXY_DIFF_GATE:-1}"
# Deterministic semantic gate: rejects touched Lean files whose vacuity count increases.
SEMANTIC_REGRESSION_GATE="${SEMANTIC_REGRESSION_GATE:-1}"
# Mandatory baseline hygiene: audited files must be committed before semantic/proxy audit.
REQUIRE_COMMITTED_BASELINE="${REQUIRE_COMMITTED_BASELINE:-1}"
REQUIRE_PUSHED_BASELINE="${REQUIRE_PUSHED_BASELINE:-1}"
AUTO_COMMIT_BEFORE_AUDIT="${AUTO_COMMIT_BEFORE_AUDIT:-0}"
AUTO_PUSH_BEFORE_AUDIT="${AUTO_PUSH_BEFORE_AUDIT:-1}"
AUTO_COMMIT_MESSAGE="${AUTO_COMMIT_MESSAGE:-proof-cleanup: commit cycle before audit}"
# Include semantic vacuity and Mathlib style/documentation audits in the loop score by default.
RUN_SEMANTIC_VACUITY_AUDIT="${RUN_SEMANTIC_VACUITY_AUDIT:-1}"
SEMANTIC_VACUITY_SCOPE="${SEMANTIC_VACUITY_SCOPE:-$SCOPE}"
RUN_STYLE_AUDIT="${RUN_STYLE_AUDIT:-1}"
STYLE_SCOPE="${STYLE_SCOPE:-$SCOPE}"
RUN_DOC_AUDIT="${RUN_DOC_AUDIT:-1}"
DOC_SCOPE="${DOC_SCOPE:-$SCOPE}"
RUN_NAMING_AUDIT="${RUN_NAMING_AUDIT:-1}"
NAMING_SCOPE="${NAMING_SCOPE:-$SCOPE}"
RUN_SEMANTIC_AUDIT="${RUN_SEMANTIC_AUDIT:-1}"
SEMANTIC_SCOPE="${SEMANTIC_SCOPE:-all}"
TOP="${TOP:-20}"
RUN_ID="${RUN_ID:-$(date -u +%Y%m%dT%H%M%SZ)}"
LOG_DIR="$ROOT/reports/cleanup-loop/$RUN_ID"
LOCK_FILE="$ROOT/reports/cleanup-loop/archon-repo-cleanup.lock"
PID_FILE="$ROOT/reports/cleanup-loop/archon-repo-cleanup.pid"
SUMMARY_FILE="$LOG_DIR/summary.tsv"

mkdir -p "$LOG_DIR" "$(dirname "$LOCK_FILE")"
cd "$ROOT"
echo $$ > "$PID_FILE"

on_interrupt() {
  local code="$?"
  echo "cleanup-loop: interrupted/exiting code=$code run_id=$RUN_ID summary=$SUMMARY_FILE" >&2
  rm -f "$PID_FILE"
  exit "$code"
}
trap on_interrupt INT TERM HUP
trap 'rm -f "$PID_FILE"' EXIT

# Archon doctor reports Pi as unconfigured if PI_CODING_AGENT is missing or set
# to a boolean sentinel. Point it at the installed Pi binary when available.
if [[ "${PI_CODING_AGENT:-}" == "" || "${PI_CODING_AGENT:-}" == "true" ]]; then
  if command -v pi >/dev/null 2>&1; then
    export PI_CODING_AGENT="$(command -v pi)"
  fi
fi

metric_value() {
  local file="$1" key="$2"
  awk -F': *' -v k="$key" '$1 == k {print $2; found=1; exit} END {if (!found) print 0}' "$file"
}

score_from_report() {
  local file="$1"
  local sorry proxy prop reexport semantic style docs naming
  sorry="$(metric_value "$file" sorry)"
  proxy="$(metric_value "$file" proxy_field)"
  prop="$(metric_value "$file" prop_interface)"
  reexport="$(metric_value "$file" reexport_proxy)"
  semantic="$(semantic_vacuity_value "$file")"
  style="$(style_violations_value "$file")"
  docs="$(doc_violations_value "$file")"
  naming="$(naming_violations_value "$file")"
  echo $((sorry + proxy + prop + reexport + semantic + style + docs + naming))
}

style_violations_value() {
  local file="$1"
  awk '
    /^Found [0-9]+ style rule violations:/ {print $2; found=1; exit}
    /No style violations found/ {print 0; found=1; exit}
    END {if (!found) print 0}
  ' "$file"
}

doc_violations_value() {
  local file="$1"
  awk '
    /^Found [0-9]+ missing docstrings:/ {print $2; found=1; exit}
    /No missing docstrings found/ {print 0; found=1; exit}
    END {if (!found) print 0}
  ' "$file"
}

semantic_vacuity_value() {
  local file="$1"
  awk '
    /^semantic_vacuity: [0-9]+/ {print $2; found=1; exit}
    END {if (!found) print 0}
  ' "$file"
}

naming_violations_value() {
  local file="$1"
  awk '
    /^Found [0-9]+ potential naming convention violations:/ {print $2; found=1; exit}
    /No naming convention violations found/ {print 0; found=1; exit}
    END {if (!found) print 0}
  ' "$file"
}

write_report() {
  local iter="$1" phase="$2" out="$3"
  {
    echo "=== cleanup-loop $RUN_ID iter=$iter phase=$phase $(date -Is) ==="
    echo "root=$ROOT scope=$SCOPE workflow=$WORKFLOW max_iterations=$MAX_ITERATIONS max_stale=$MAX_STALE_ITERATIONS stop_when_clean=$STOP_WHEN_CLEAN timeout=$ARCHON_CYCLE_TIMEOUT_SECONDS interval=$INTERVAL_SECONDS post_tick=${POST_TICK_COMMAND:-none} proxy_diff_gate=$PROOF_PROXY_DIFF_GATE semantic_regression_gate=$SEMANTIC_REGRESSION_GATE semantic_vacuity_audit=$RUN_SEMANTIC_VACUITY_AUDIT semantic_scope=$SEMANTIC_VACUITY_SCOPE style_audit=$RUN_STYLE_AUDIT style_scope=$STYLE_SCOPE doc_audit=$RUN_DOC_AUDIT doc_scope=$DOC_SCOPE naming_audit=$RUN_NAMING_AUDIT naming_scope=$NAMING_SCOPE"
    python3 tools/quality/proof_heartbeat.py "$SCOPE" --top "$TOP" || true
    echo
    python3 tools/lean4-skills/sorry_analyzer.py "$SCOPE" --format=summary || true
    if [[ "$RUN_SEMANTIC_VACUITY_AUDIT" == "1" ]]; then
      echo
      python3 tools/quality/semantic_vacuity_gate.py "$SEMANTIC_VACUITY_SCOPE" --fail-on none --top "$TOP" || true
    fi
    if [[ "$RUN_STYLE_AUDIT" == "1" ]]; then
      echo
      python3 tools/quality/audit_style.py "$STYLE_SCOPE" || true
    fi
    if [[ "$RUN_DOC_AUDIT" == "1" ]]; then
      echo
      python3 tools/quality/audit_docstrings.py "$DOC_SCOPE" || true
    fi
    if [[ "$RUN_NAMING_AUDIT" == "1" ]]; then
      echo
      python3 tools/quality/audit_naming.py "$NAMING_SCOPE" || true
    fi
    if [[ "$RUN_SEMANTIC_AUDIT" == "1" ]]; then
      echo
      python3 tools/quality/semantic_content_audit.py --scope "$SEMANTIC_SCOPE" --gate-review || true
    fi
  } > "$out" 2>&1
}

append_summary() {
  local iter="$1" phase="$2" report="$3"
  local sorry proxy prop reexport semantic style docs naming score
  sorry="$(metric_value "$report" sorry)"
  proxy="$(metric_value "$report" proxy_field)"
  prop="$(metric_value "$report" prop_interface)"
  reexport="$(metric_value "$report" reexport_proxy)"
  semantic="$(semantic_vacuity_value "$report")"
  style="$(style_violations_value "$report")"
  docs="$(doc_violations_value "$report")"
  naming="$(naming_violations_value "$report")"
  score=$((sorry + proxy + prop + reexport + semantic + style + docs + naming))
  printf "%s\t%s\t%s\t%s\t%s\t%s\t%s\t%s\t%s\t%s\t%s\t%s\n" \
    "$iter" "$phase" "$sorry" "$proxy" "$prop" "$reexport" "$semantic" "$style" "$docs" "$naming" "$score" "$report" >> "$SUMMARY_FILE"
}

run_archon_workflow() {
  if [[ -d "$ROOT/archon" ]] && command -v bun >/dev/null 2>&1; then
    (cd "$ROOT/archon" && bun run cli workflow run "$WORKFLOW" --cwd "$ROOT" --no-worktree)
  else
    archon workflow run "$WORKFLOW" --cwd "$ROOT" --no-worktree
  fi
}

run_archon_cycle() {
  if [[ "$ARCHON_CYCLE_TIMEOUT_SECONDS" -gt 0 ]]; then
    ROOT="$ROOT" WORKFLOW="$WORKFLOW" timeout "$ARCHON_CYCLE_TIMEOUT_SECONDS" bash -lc '
      if [[ -d "$ROOT/archon" ]] && command -v bun >/dev/null 2>&1; then
        cd "$ROOT/archon" && bun run cli workflow run "$WORKFLOW" --cwd "$ROOT" --no-worktree
      else
        archon workflow run "$WORKFLOW" --cwd "$ROOT" --no-worktree
      fi
    '
  else
    run_archon_workflow
  fi
}

run_proxy_diff_gate() {
  local iter="$1" base="$2"
  local out="$LOG_DIR/iter-$(printf '%03d' "$iter")-proxy-diff-gate.log"
  if [[ "$PROOF_PROXY_DIFF_GATE" == "1" ]]; then
    {
      echo "=== proof proxy diff gate iter=$iter $(date -Is) ==="
      echo "base=$base scope=$SCOPE"
      python3 tools/quality/proof_proxy_diff_gate.py --base "$base" "$SCOPE"
      echo "=== proof proxy diff gate done iter=$iter $(date -Is) ==="
    } > "$out" 2>&1
  fi
}

run_semantic_regression_gate() {
  local iter="$1" base="$2"
  local out="$LOG_DIR/iter-$(printf '%03d' "$iter")-semantic-regression-gate.log"
  if [[ "$SEMANTIC_REGRESSION_GATE" == "1" ]]; then
    {
      echo "=== semantic regression gate iter=$iter $(date -Is) ==="
      echo "base=$base scope=$SCOPE"
      python3 tools/quality/semantic_regression_gate.py --base "$base" "$SCOPE"
      echo "=== semantic regression gate done iter=$iter $(date -Is) ==="
    } > "$out" 2>&1
  fi
}

run_committed_baseline_gate() {
  local iter="$1" phase="$2"
  local out="$LOG_DIR/iter-$(printf '%03d' "$iter")-$phase-committed-baseline-gate.log"
  if [[ "$REQUIRE_COMMITTED_BASELINE" == "1" ]]; then
    {
      echo "=== committed baseline gate iter=$iter phase=$phase $(date -Is) ==="
      local args=()
      if [[ "$REQUIRE_PUSHED_BASELINE" == "1" ]]; then
        args+=(--require-pushed)
      fi
      python3 tools/quality/committed_baseline_gate.py "$SCOPE" "${args[@]}"
      echo "=== committed baseline gate done iter=$iter phase=$phase $(date -Is) ==="
    } > "$out" 2>&1
  fi
}

scope_has_changes() {
  ! git diff --quiet -- "$SCOPE" ||
    ! git diff --cached --quiet -- "$SCOPE" ||
    [[ -n "$(git ls-files --others --exclude-standard -- "$SCOPE")" ]]
}

commit_scope_before_audit() {
  local iter="$1"
  local out="$LOG_DIR/iter-$(printf '%03d' "$iter")-commit-before-audit.log"
  if [[ "$AUTO_COMMIT_BEFORE_AUDIT" == "1" ]] && scope_has_changes; then
    {
      echo "=== commit before audit iter=$iter $(date -Is) ==="
      git add -A -- "$SCOPE"
      git commit -m "$AUTO_COMMIT_MESSAGE"
      if [[ "$AUTO_PUSH_BEFORE_AUDIT" == "1" ]]; then
        git push
      fi
      echo "=== commit before audit done iter=$iter $(date -Is) ==="
    } > "$out" 2>&1
  fi
}

run_post_tick_command() {
  local iter="$1"
  local out="$LOG_DIR/iter-$(printf '%03d' "$iter")-post-tick.log"
  if [[ -n "$POST_TICK_COMMAND" ]]; then
    {
      echo "=== post-tick command iter=$iter $(date -Is) ==="
      echo "$POST_TICK_COMMAND"
      bash -lc "$POST_TICK_COMMAND"
      echo "=== post-tick command done iter=$iter $(date -Is) ==="
    } > "$out" 2>&1 || {
      local code=$?
      echo "cleanup-loop: post-tick command exited code=$code; see $out" | tee -a "$out"
    }
  fi
}

if [[ ! -f "$SUMMARY_FILE" ]]; then
  printf "iter\tphase\tsorry\tproxy_field\tprop_interface\treexport_proxy\tsemantic_vacuity\tstyle_violations\tdocstring_violations\tnaming_violations\tscore\treport\n" > "$SUMMARY_FILE"
fi

best_score=999999999
stale_iterations=0
iter=1

while true; do
  if [[ "$MAX_ITERATIONS" -gt 0 && "$iter" -gt "$MAX_ITERATIONS" ]]; then
    echo "cleanup-loop: reached MAX_ITERATIONS=$MAX_ITERATIONS. summary=$SUMMARY_FILE"
    exit 3
  fi

  before="$LOG_DIR/iter-$(printf '%03d' "$iter")-before.log"
  after="$LOG_DIR/iter-$(printf '%03d' "$iter")-after.log"
  archon_log="$LOG_DIR/iter-$(printf '%03d' "$iter")-archon.log"
  baseline_ref="$(git rev-parse HEAD)"

  if ! run_committed_baseline_gate "$iter" before; then
    echo "cleanup-loop: committed baseline gate failed before audit. commit and push audited files first; see $LOG_DIR/iter-$(printf '%03d' "$iter")-before-committed-baseline-gate.log"
    exit 92
  fi
  write_report "$iter" before "$before"
  append_summary "$iter" before "$before"
  before_score="$(score_from_report "$before")"

  if [[ "$before_score" -eq 0 ]]; then
    echo "cleanup-loop: clean before iteration $iter; continuing heartbeat. summary=$SUMMARY_FILE"
    if [[ "$STOP_WHEN_CLEAN" == "1" ]]; then
      echo "cleanup-loop: STOP_WHEN_CLEAN=1; stopping. summary=$SUMMARY_FILE"
      exit 0
    fi
  fi

  if ! flock -n 9; then
    echo "cleanup-loop: another cleanup loop is active; lock=$LOCK_FILE" | tee -a "$archon_log"
    exit 75
  fi

  {
    echo "=== archon workflow run iter=$iter $(date -Is) ==="
    echo "before_score=$before_score"
    run_archon_cycle
    echo "=== archon workflow done iter=$iter $(date -Is) ==="
  } > "$archon_log" 2>&1 || {
    code=$?
    echo "cleanup-loop: workflow exited nonzero/timeout code=$code; see $archon_log" | tee -a "$archon_log"
  }
  flock -u 9

  commit_scope_before_audit "$iter"

  if ! run_committed_baseline_gate "$iter" after; then
    echo "cleanup-loop: committed baseline gate failed after workflow. commit and push audited files before semantic/proxy audit; no files were restored. see $LOG_DIR/iter-$(printf '%03d' "$iter")-after-committed-baseline-gate.log"
    exit 92
  fi

  after_ref="$(git rev-parse HEAD)"
  if [[ "$after_ref" != "$baseline_ref" ]]; then
    if ! run_proxy_diff_gate "$iter" "$baseline_ref"; then
      echo "cleanup-loop: proof proxy diff gate failed against committed ref $baseline_ref..HEAD; no files were restored. see $LOG_DIR/iter-$(printf '%03d' "$iter")-proxy-diff-gate.log"
      exit 90
    fi

    if ! run_semantic_regression_gate "$iter" "$baseline_ref"; then
      echo "cleanup-loop: semantic regression gate failed against committed ref $baseline_ref..HEAD; no files were restored. see $LOG_DIR/iter-$(printf '%03d' "$iter")-semantic-regression-gate.log"
      exit 91
    fi
  fi

  write_report "$iter" after "$after"
  append_summary "$iter" after "$after"
  after_score="$(score_from_report "$after")"

  run_post_tick_command "$iter"

  if [[ "$after_score" -eq 0 ]]; then
    echo "cleanup-loop: clean after iteration $iter; continuing heartbeat. summary=$SUMMARY_FILE"
    if [[ "$STOP_WHEN_CLEAN" == "1" ]]; then
      echo "cleanup-loop: STOP_WHEN_CLEAN=1; stopping. summary=$SUMMARY_FILE"
      exit 0
    fi
  fi

  if [[ "$after_score" -lt "$best_score" ]]; then
    best_score="$after_score"
    stale_iterations=0
  else
    stale_iterations=$((stale_iterations + 1))
  fi

  if [[ "$MAX_STALE_ITERATIONS" -gt 0 && "$stale_iterations" -ge "$MAX_STALE_ITERATIONS" ]]; then
    echo "cleanup-loop: stopped after $stale_iterations stale iterations; best_score=$best_score summary=$SUMMARY_FILE"
    exit 2
  fi

  if [[ "$INTERVAL_SECONDS" -gt 0 ]]; then
    sleep "$INTERVAL_SECONDS"
  fi

  iter=$((iter + 1))
done 9>"$LOCK_FILE"
