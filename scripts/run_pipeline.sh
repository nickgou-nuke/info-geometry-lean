#!/usr/bin/env bash
# scripts/run_pipeline.sh
#
# Deterministic, lock-serialized pipeline runner for the ontology / taxonomy /
# phylogenesis pipeline (QMS-PLAN-PIPE-001, Phase 5).
#
# Stages:
#   1. Narrow locked Lean build on ontology/taxonomy/phylogenesis owners
#   2. Python taxonomy & cross-layer contract tests
#   3. Phylogeny export + dashboard generation (from live git log or JSON fixture)
#   4. ArangoDB -> Auto-Ontology bridge dry-run (offline) or generation-pinned projection
#
# Emits artifacts/pipeline_runs/<UTC_TIMESTAMP>_<SHORT_SHA>/run_receipt.json
# with git_head, git_status_clean, per-stage exit codes, durations, and SHA-256
# artifact digests.
#
# Usage:
#   scripts/run_pipeline.sh [--skip-lean-build] [--generation-id <ID>] [--report-dir <DIR>]
#
set -euo pipefail

SCRIPT_DIR_ABS="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
ROOT="$(cd "$SCRIPT_DIR_ABS/.." && pwd)"
cd "$ROOT"

SKIP_LEAN_BUILD=false
GENERATION_ID=""
REPORT_DIR=""

for arg in "$@"; do
    case "$arg" in
        --skip-lean-build)
            SKIP_LEAN_BUILD=true
            ;;
        --generation-id=*)
            GENERATION_ID="${arg#*=}"
            ;;
        --generation-id)
            echo "error: --generation-id requires an argument" >&2
            exit 2
            ;;
        --report-dir=*)
            REPORT_DIR="${arg#*=}"
            ;;
        --report-dir)
            echo "error: --report-dir requires an argument" >&2
            exit 2
            ;;
        --help|-h)
            echo "Usage: $0 [--skip-lean-build] [--generation-id <ID>] [--report-dir <DIR>]"
            exit 0
            ;;
        *)
            echo "error: unknown argument: $arg" >&2
            exit 2
            ;;
    esac
done

if [ -z "$REPORT_DIR" ]; then
    UTC_TIMESTAMP="$(date -u '+%Y%m%dT%H%M%SZ')"
    SHORT_SHA="$(git rev-parse --short HEAD 2>/dev/null || echo 'unknown')"
    REPORT_DIR="artifacts/pipeline_runs/${UTC_TIMESTAMP}_${SHORT_SHA}"
fi
REPORT_DIR="$(cd "$ROOT" && mkdir -p "$REPORT_DIR" && cd "$REPORT_DIR" && pwd)"

mkdir -p "$REPORT_DIR"

RECEIPT_FILE="$REPORT_DIR/run_receipt.json"
GIT_HEAD="$(git rev-parse HEAD 2>/dev/null || echo 'unknown')"
GIT_STATUS_CLEAN="false"
if git diff --quiet && git diff --cached --quiet && [ -z "$(git ls-files --others --exclude-standard)" ]; then
    GIT_STATUS_CLEAN="true"
fi

# ---------------------------------------------------------------------------
# Stage timing helper
# ---------------------------------------------------------------------------
stage_start() { echo "$(date +%s)"; }
stage_elapsed() { local start="$1"; echo $(( $(date +%s) - start )); }

# ---------------------------------------------------------------------------
# Receipt assembly
# ---------------------------------------------------------------------------
declare -A STAGE_EXIT_CODES
declare -A STAGE_DURATIONS
STAGE_EXIT_CODES["lean_build"]=""
STAGE_EXIT_CODES["taxonomy_tests"]=""
STAGE_EXIT_CODES["phylogeny_export"]=""
STAGE_EXIT_CODES["dashboard"]=""
STAGE_EXIT_CODES["ontology_bridge"]=""

overall_exit=0

run_stage() {
    local stage_name="$1"; shift
    local start
    start="$(stage_start)"
    set +e
    "$@"
    local code=$?
    set -e
    STAGE_EXIT_CODES["$stage_name"]="$code"
    STAGE_DURATIONS["$stage_name"]="$(stage_elapsed "$start")"
    if [ "$code" -ne 0 ]; then
        echo "  ❌ Stage '$stage_name' failed (exit code: $code)"
        overall_exit=1
    else
        echo "  ✅ Stage '$stage_name' passed (${STAGE_DURATIONS[$stage_name]}s)"
    fi
}

sha256_file() {
    local f="$1"
    if [ -f "$f" ]; then
        sha256sum "$f" | awk '{print $1}'
    else
        echo "absent"
    fi
}

echo "═══════════════════════════════════════════════════════════════════════════════"
echo "  QMS-PLAN-PIPE-001 Phase 5 Pipeline Runner"
echo "═══════════════════════════════════════════════════════════════════════════════"
echo "Root:          $ROOT"
echo "Git HEAD:      $GIT_HEAD"
echo "Git clean:     $GIT_STATUS_CLEAN"
echo "Report dir:    $REPORT_DIR"
echo

# ---------------------------------------------------------------------------
# Stage 1: Narrow locked Lean build
# ---------------------------------------------------------------------------
if [ "$SKIP_LEAN_BUILD" = "true" ]; then
    echo "⏩ Skipping Lean build (--skip-lean-build)"
    STAGE_EXIT_CODES["lean_build"]="skipped"
else
    echo "▶ Stage 1: Narrow locked Lean build (ontology/taxonomy/phylogenesis owners)"
    run_stage "lean_build" \
        python3 tools/infra/run_locked_lake_build.py \
            --wait-for-build-lock \
            InfoGeometry.OperatorAlgebra.PeirceSpine.CladisticPhylogenesisBridge \
            InfoGeometry.OperatorAlgebra.OntologyRing \
            InfoGeometry.Canonical.AnalyticOntologyTaxonomyPhylogenesisPoset \
            InfoGeometry.Canonical.AnalyticOntologyTaxonomyPhylogenesisPosetAudit \
            InfoGeometry.Graph.DarwinCommitTaxonomy
fi

# ---------------------------------------------------------------------------
# Stage 2: Python taxonomy & cross-layer contract tests
# ---------------------------------------------------------------------------
echo "▶ Stage 2: Python taxonomy & cross-layer contract tests"
PY_TEST_BIN="python3"
if [ -x "$ROOT/external_refs/auto-ontology/.venv/bin/python" ]; then
    PY_TEST_BIN="$ROOT/external_refs/auto-ontology/.venv/bin/python"
elif [ -x "$ROOT/.venv-py312/bin/python" ]; then
    PY_TEST_BIN="$ROOT/.venv-py312/bin/python"
fi
run_stage "taxonomy_tests" \
    env PYTHONPATH="$ROOT/src:$ROOT" "$PY_TEST_BIN" -m pytest \
        tests/test_evolution_taxonomy.py \
        tests/test_repository_phylogeny_export.py \
        tests/test_darwin_phylogeny_dashboard.py \
        tests/test_decl_graph_generation.py \
        tests/test_ontology_term_integrity.py \
        tests/test_ontology_relationship_identity.py \
        tests/test_arango_ontology_bridge.py \
        -v

# ---------------------------------------------------------------------------
# Stage 3: Phylogeny export + dashboard generation
# ---------------------------------------------------------------------------
echo "▶ Stage 3: Phylogeny export + dashboard generation"
PHYLOGENY_JSON="$REPORT_DIR/phylogeny_export.json"
DASHBOARD_HTML="$REPORT_DIR/darwin_phylogeny.html"
run_stage "phylogeny_export" \
    python3 tools/repository_evolution/phylogeny_export.py \
        --repo "$ROOT" \
        --since "2026-01-01" \
        --until "2026-12-31" \
        --repository-url "$(git remote get-url origin 2>/dev/null || echo 'https://github.com/example/repo')" \
        --out "$PHYLOGENY_JSON"
run_stage "dashboard" \
    "$PY_TEST_BIN" tools/infra/darwin_phylogeny_dashboard.py \
        --phylogeny-json "$PHYLOGENY_JSON" \
        --out "$DASHBOARD_HTML"

# ---------------------------------------------------------------------------
# Stage 4: ArangoDB -> Auto-Ontology bridge (dry-run offline or generation-pinned)
# ---------------------------------------------------------------------------
echo "▶ Stage 4: ArangoDB -> Auto-Ontology bridge"
BRIDGE_JSONL="$REPORT_DIR/bridge_decls.jsonl"
BRIDGE_REPORT="$REPORT_DIR/bridge_report.json"
# Build an offline JSONL fixture from the phylogeny export for dry-run validation.
python3 - "$PHYLOGENY_JSON" "$BRIDGE_JSONL" <<'PYEOF'
import json, sys, os
sys.path.insert(0, os.path.join(os.getcwd(), 'src'))
from igf.graph.decl_schema import decl_key
src, dst = sys.argv[1], sys.argv[2]
data = json.loads(open(src).read())
records = []
for row in data.get("commits", []):
    name = f"{row.get('sha','unknown')[:12]}"
    records.append({
        "name": name,
        "kind": "commit",
        "doc": row.get("subject", ""),
        "module": "GitHistory",
        "relFile": "GIT",
        "line": 0,
        "_key": decl_key(name),
    })
with open(dst, "w") as f:
    for rec in records:
        f.write(json.dumps(rec) + "\n")
print(f"Wrote {len(records)} declaration records to {dst}")
PYEOF
run_stage "ontology_bridge" \
    python3 tools/infra/arango_to_ontology.py \
        --dry-run \
        --decls-jsonl "$BRIDGE_JSONL" \
        --report-json "$BRIDGE_REPORT"

# ---------------------------------------------------------------------------
# Write run_receipt.json
# ---------------------------------------------------------------------------
python3 - "$RECEIPT_FILE" "$GIT_HEAD" "$GIT_STATUS_CLEAN" "$REPORT_DIR" \
    "$PHYLOGENY_JSON" "$DASHBOARD_HTML" "$BRIDGE_JSONL" "$BRIDGE_REPORT" \
    "${STAGE_EXIT_CODES["lean_build"]:-null}" "${STAGE_DURATIONS["lean_build"]:-null}" \
    "${STAGE_EXIT_CODES["taxonomy_tests"]:-null}" "${STAGE_DURATIONS["taxonomy_tests"]:-null}" \
    "${STAGE_EXIT_CODES["phylogeny_export"]:-null}" "${STAGE_DURATIONS["phylogeny_export"]:-null}" \
    "${STAGE_EXIT_CODES["dashboard"]:-null}" "${STAGE_DURATIONS["dashboard"]:-null}" \
    "${STAGE_EXIT_CODES["ontology_bridge"]:-null}" "${STAGE_DURATIONS["ontology_bridge"]:-null}" \
    "$overall_exit" <<'PYEOF'
import json, sys, os, hashlib
(receipt_file, git_head, git_status_clean, report_dir,
 phylogeny_json, dashboard_html, bridge_jsonl, bridge_report,
 lean_ec, lean_dur, tax_ec, tax_dur, phylo_ec, phylo_dur,
 dash_ec, dash_dur, bridge_ec, bridge_dur, overall_exit) = sys.argv[1:]

def sha256_file(path):
    if path and os.path.isfile(path):
        with open(path, 'rb') as f:
            return hashlib.sha256(f.read()).hexdigest()
    return "absent"

receipt = {
    "schema": "info_geometry.pipeline_run_receipt.v1",
    "generated_at": __import__('datetime').datetime.utcnow().strftime('%Y-%m-%dT%H:%M:%SZ') + 'Z',
    "git_head": git_head,
    "git_status_clean": git_status_clean == 'true',
    "report_dir": report_dir,
    "stages": {
        "lean_build": {"exit_code": lean_ec if lean_ec in ('skipped', 'null', None) else int(lean_ec),
                       "duration_seconds": int(lean_dur) if lean_dur and lean_dur not in ('skipped', 'null', None) else None},
        "taxonomy_tests": {"exit_code": int(tax_ec) if tax_ec and tax_ec != 'null' else None,
                           "duration_seconds": int(tax_dur) if tax_dur and tax_dur != 'null' else None},
        "phylogeny_export": {"exit_code": int(phylo_ec) if phylo_ec and phylo_ec != 'null' else None,
                             "duration_seconds": int(phylo_dur) if phylo_dur and phylo_dur != 'null' else None},
        "dashboard": {"exit_code": int(dash_ec) if dash_ec and dash_ec != 'null' else None,
                      "duration_seconds": int(dash_dur) if dash_dur and dash_dur != 'null' else None},
        "ontology_bridge": {"exit_code": int(bridge_ec) if bridge_ec and bridge_ec != 'null' else None,
                            "duration_seconds": int(bridge_dur) if bridge_dur and bridge_dur != 'null' else None},
    },
    "artifacts": {
        "phylogeny_export": phylogeny_json,
        "dashboard_html": dashboard_html,
        "bridge_jsonl": bridge_jsonl,
        "bridge_report": bridge_report,
    },
    "artifact_digests": {
        "phylogeny_export": sha256_file(phylogeny_json),
        "dashboard_html": sha256_file(dashboard_html),
        "bridge_jsonl": sha256_file(bridge_jsonl),
        "bridge_report": sha256_file(bridge_report),
    },
    "overall_exit_code": int(overall_exit),
}
with open(receipt_file, 'w') as f:
    json.dump(receipt, f, indent=2)
    f.write('\n')
PYEOF

echo
echo "═══════════════════════════════════════════════════════════════════════════════"
if [ "$overall_exit" -eq 0 ]; then
    echo "  ✅ ALL PIPELINE STAGES PASSED"
else
    echo "  ❌ SOME PIPELINE STAGES FAILED"
fi
echo "Receipt: $RECEIPT_FILE"
echo "═══════════════════════════════════════════════════════════════════════════════"

exit "$overall_exit"
