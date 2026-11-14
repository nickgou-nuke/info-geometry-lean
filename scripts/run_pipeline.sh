#!/usr/bin/env bash
# scripts/run_pipeline.sh
#
# Deterministic, lock-serialized pipeline runner for the ontology / taxonomy /
# phylogenesis pipeline (QMS-PLAN-PIPE-001, Phase 5).
#
# Stages:
#   1. Narrow locked Lean build on ontology/taxonomy/phylogenesis owners
#   2. Offline Python regression tests
#   3. Current-source ontology map, all-ref change extraction, weak labels, and habitats
#   4. Git commit phylogeny export and carrier-separated dashboard
#   5. ArangoDB -> Auto-Ontology read-only preflight (offline fixture or generation)
#
# Emits artifacts/pipeline_runs/<UTC_TIMESTAMP>_<SHORT_SHA>/run_receipt.json
# with git_head, git_status_clean, per-stage exit codes, durations, and SHA-256
# artifact digests.
#
# Usage:
#   scripts/run_pipeline.sh [--skip-lean-build] [--generation-id <ID>]
#       [--since <UTC>] [--until <UTC>] [--report-dir <DIR>]
#   PIPELINE_PYTHON_BIN=/path/to/python can select the Python runtime.
#
set -euo pipefail

SCRIPT_DIR_ABS="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
ROOT="$(cd "$SCRIPT_DIR_ABS/.." && pwd)"
cd "$ROOT"

SKIP_LEAN_BUILD=false
GENERATION_ID=""
GENERATION_ID_SET=false
REPORT_DIR=""
CURRENT_YEAR="$(date -u '+%Y')"
SINCE="${CURRENT_YEAR}-01-01T00:00:00Z"
NEXT_YEAR="$((CURRENT_YEAR + 1))"
UNTIL="${NEXT_YEAR}-01-01T00:00:00Z"
PIPELINE_PYTHON_BIN="${PIPELINE_PYTHON_BIN:-python3}"

while (($#)); do
    case "$1" in
        --skip-lean-build)
            SKIP_LEAN_BUILD=true
            shift
            ;;
        --generation-id)
            if (($# < 2)); then echo "error: --generation-id requires an argument" >&2; exit 2; fi
            GENERATION_ID="$2"
            GENERATION_ID_SET=true
            shift 2
            ;;
        --generation-id=*)
            GENERATION_ID="${1#*=}"
            GENERATION_ID_SET=true
            shift
            ;;
        --since)
            if (($# < 2)); then echo "error: --since requires an argument" >&2; exit 2; fi
            SINCE="$2"
            shift 2
            ;;
        --since=*)
            SINCE="${1#*=}"
            shift
            ;;
        --until)
            if (($# < 2)); then echo "error: --until requires an argument" >&2; exit 2; fi
            UNTIL="$2"
            shift 2
            ;;
        --until=*)
            UNTIL="${1#*=}"
            shift
            ;;
        --report-dir)
            if (($# < 2)); then echo "error: --report-dir requires an argument" >&2; exit 2; fi
            REPORT_DIR="$2"
            shift 2
            ;;
        --report-dir=*)
            REPORT_DIR="${1#*=}"
            shift
            ;;
        --help|-h)
            echo "Usage: $0 [--skip-lean-build] [--generation-id <ID>] [--since <UTC>] [--until <UTC>] [--report-dir <DIR>]"
            exit 0
            ;;
        *)
            echo "error: unknown argument: $1" >&2
            exit 2
            ;;
    esac
done

if [ "$GENERATION_ID_SET" = "true" ] && [ -z "$GENERATION_ID" ]; then
    echo "error: --generation-id must not be empty" >&2
    exit 2
fi

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
STAGE_EXIT_CODES["source_ontology"]=""
STAGE_EXIT_CODES["commit_path_extraction"]=""
STAGE_EXIT_CODES["weak_commit_taxonomy"]=""
STAGE_EXIT_CODES["path_habitats"]=""
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
        "$PIPELINE_PYTHON_BIN" tools/infra/run_locked_lake_build.py \
            --wait-for-build-lock \
            InfoGeometry.OperatorAlgebra.PeirceSpine.CladisticPhylogenesisBridge \
            InfoGeometry.OperatorAlgebra.OntologyRing \
            InfoGeometry.Canonical.AnalyticOntologyTaxonomyPhylogenesisPoset \
            InfoGeometry.Canonical.AnalyticOntologyTaxonomyPhylogenesisPosetAudit \
            InfoGeometry.Graph.DarwinCommitTaxonomy
fi

# ---------------------------------------------------------------------------
# Stage 2: Offline Python regression tests
# ---------------------------------------------------------------------------
echo "▶ Stage 2: offline Python regression tests"
PY_TEST_BIN="${PIPELINE_PYTEST_BIN:-$PIPELINE_PYTHON_BIN}"
if [ -z "${PIPELINE_PYTEST_BIN:-}" ]; then
    if [ -x "$ROOT/external_refs/auto-ontology/.venv/bin/python" ]; then
        PY_TEST_BIN="$ROOT/external_refs/auto-ontology/.venv/bin/python"
    elif [ -x "$ROOT/.venv-py312/bin/python" ]; then
        PY_TEST_BIN="$ROOT/.venv-py312/bin/python"
    fi
fi
run_stage "taxonomy_tests" \
    env PYTHONPATH="$ROOT/src:$ROOT" "$PY_TEST_BIN" -m pytest \
        tests/test_evolution_taxonomy.py \
        tests/test_repository_phylogeny_export.py \
        tests/test_darwin_phylogeny_dashboard.py \
        tests/test_refactoring_map.py \
        tests/test_evolution_metadata_only.py \
        tests/test_decl_graph_generation.py \
        tests/test_ontology_term_integrity.py \
        tests/test_ontology_relationship_identity.py \
        tests/test_arango_ontology_bridge.py \
        -v

# ---------------------------------------------------------------------------
# Stage 3: Current-source ontology map and commit-label artifacts
# ---------------------------------------------------------------------------
SOURCE_MAP="$REPORT_DIR/source_ontology.json.gz"
EVOLUTION_DIR="$REPORT_DIR/evolution"
mkdir -p "$EVOLUTION_DIR"
echo "▶ Stage 3a: current-source ontology map"
run_stage "source_ontology" \
    "$PIPELINE_PYTHON_BIN" tools/repository_evolution/refactoring_map.py \
        --out "$SOURCE_MAP"
TAXONOMY_COMMITS="$EVOLUTION_DIR/commits.jsonl"
TAXONOMY_PATHS="$EVOLUTION_DIR/paths.jsonl"
TAXONOMY_NUMSTAT="$EVOLUTION_DIR/numstat.jsonl"
TAXONOMY_LABELS="$EVOLUTION_DIR/labels.jsonl"
TAXONOMY_HABITATS="$EVOLUTION_DIR/habitats.json"
echo "▶ Stage 3b: all-ref Git commit/path/numstat extraction"
run_stage "commit_path_extraction" \
    "$PIPELINE_PYTHON_BIN" tools/infra/evolution_extract.py "$TAXONOMY_COMMITS" \
        --repo "$ROOT" --paths-output "$TAXONOMY_PATHS" \
        --numstat-output "$TAXONOMY_NUMSTAT"
echo "▶ Stage 3c: weak commit taxonomy labels"
run_stage "weak_commit_taxonomy" \
    "$PIPELINE_PYTHON_BIN" tools/infra/evolution_taxonomy.py "$TAXONOMY_COMMITS" \
        --paths "$TAXONOMY_PATHS" --out "$TAXONOMY_LABELS"
echo "▶ Stage 3d: path-habitat summaries"
run_stage "path_habitats" \
    "$PIPELINE_PYTHON_BIN" tools/infra/evolution_path_habitat.py "$TAXONOMY_PATHS" \
        --out "$TAXONOMY_HABITATS"

# ---------------------------------------------------------------------------
# Stage 4: Phylogeny export + carrier-separated dashboard
# ---------------------------------------------------------------------------
echo "▶ Stage 4: phylogeny export + combined dashboard"
PHYLOGENY_JSON="$REPORT_DIR/phylogeny_export.json"
DASHBOARD_HTML="$REPORT_DIR/darwin_phylogeny.html"
run_stage "phylogeny_export" \
    "$PIPELINE_PYTHON_BIN" tools/repository_evolution/phylogeny_export.py \
        --repo "$ROOT" \
        --since "$SINCE" \
        --until "$UNTIL" \
        --repository-url "$(git remote get-url origin 2>/dev/null || echo 'https://github.com/example/repo')" \
        --out "$PHYLOGENY_JSON"
run_stage "dashboard" \
    "$PY_TEST_BIN" tools/infra/darwin_phylogeny_dashboard.py \
        --phylogeny-json "$PHYLOGENY_JSON" \
        --labels "$TAXONOMY_LABELS" \
        --source-map "$SOURCE_MAP" \
        --out "$DASHBOARD_HTML"

# ---------------------------------------------------------------------------
# Stage 5: Read-only ontology bridge preflight
# ---------------------------------------------------------------------------
echo "▶ Stage 5: ontology bridge read-only preflight"
BRIDGE_JSONL="$REPORT_DIR/bridge_decls.jsonl"
BRIDGE_EDGES_JSONL="$REPORT_DIR/bridge_edges.jsonl"
BRIDGE_REPORT="$REPORT_DIR/bridge_report.json"
BRIDGE_RELATIONSHIP_REPORT="$REPORT_DIR/bridge_relationship_report.json"
bridge_preflight() {
    if [ -n "$GENERATION_ID" ]; then
        "$PIPELINE_PYTHON_BIN" tools/infra/arango_to_ontology.py \
            --dry-run --generation-id "$GENERATION_ID" \
            --report-json "$BRIDGE_REPORT" || return $?
        "$PIPELINE_PYTHON_BIN" tools/infra/arango_to_ontology_relationships.py \
            --dry-run --generation-id "$GENERATION_ID" \
            --report-json "$BRIDGE_RELATIONSHIP_REPORT" || return $?
        return 0
    fi
    # This synthetic commit-shaped fixture checks only the offline bridge contract;
    # it is not a projection of Arango declarations or a live ontology refresh.
    "$PIPELINE_PYTHON_BIN" - "$PHYLOGENY_JSON" "$BRIDGE_JSONL" "$BRIDGE_EDGES_JSONL" <<'PYEOF' || return $?
import json, sys, os
sys.path.insert(0, os.path.join(os.getcwd(), 'src'))
from igf.graph.decl_schema import decl_key
src, dst, edges_dst = sys.argv[1], sys.argv[2], sys.argv[3]
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
open(edges_dst, "w").close()
print(f"Wrote {len(records)} synthetic dry-run records to {dst}")
PYEOF
    "$PIPELINE_PYTHON_BIN" tools/infra/arango_to_ontology.py \
        --dry-run --decls-jsonl "$BRIDGE_JSONL" --edges-jsonl "$BRIDGE_EDGES_JSONL" \
        --report-json "$BRIDGE_REPORT" || return $?
    "$PIPELINE_PYTHON_BIN" tools/infra/arango_to_ontology_relationships.py \
        --dry-run --decls-jsonl "$BRIDGE_JSONL" --edges-jsonl "$BRIDGE_EDGES_JSONL" \
        --report-json "$BRIDGE_RELATIONSHIP_REPORT"
}
run_stage "ontology_bridge" bridge_preflight

# ---------------------------------------------------------------------------
# Write run_receipt.json
# ---------------------------------------------------------------------------
"$PIPELINE_PYTHON_BIN" - "$RECEIPT_FILE" "$GIT_HEAD" "$GIT_STATUS_CLEAN" "$REPORT_DIR" \
    "$SOURCE_MAP" "$TAXONOMY_COMMITS" "$TAXONOMY_PATHS" "$TAXONOMY_NUMSTAT" \
    "$TAXONOMY_LABELS" "$TAXONOMY_HABITATS" "$PHYLOGENY_JSON" "$DASHBOARD_HTML" \
    "$BRIDGE_JSONL" "$BRIDGE_EDGES_JSONL" "$BRIDGE_REPORT" "$BRIDGE_RELATIONSHIP_REPORT" \
    "${STAGE_EXIT_CODES["lean_build"]:-null}" "${STAGE_DURATIONS["lean_build"]:-null}" \
    "${STAGE_EXIT_CODES["taxonomy_tests"]:-null}" "${STAGE_DURATIONS["taxonomy_tests"]:-null}" \
    "${STAGE_EXIT_CODES["source_ontology"]:-null}" "${STAGE_DURATIONS["source_ontology"]:-null}" \
    "${STAGE_EXIT_CODES["commit_path_extraction"]:-null}" "${STAGE_DURATIONS["commit_path_extraction"]:-null}" \
    "${STAGE_EXIT_CODES["weak_commit_taxonomy"]:-null}" "${STAGE_DURATIONS["weak_commit_taxonomy"]:-null}" \
    "${STAGE_EXIT_CODES["path_habitats"]:-null}" "${STAGE_DURATIONS["path_habitats"]:-null}" \
    "${STAGE_EXIT_CODES["phylogeny_export"]:-null}" "${STAGE_DURATIONS["phylogeny_export"]:-null}" \
    "${STAGE_EXIT_CODES["dashboard"]:-null}" "${STAGE_DURATIONS["dashboard"]:-null}" \
    "${STAGE_EXIT_CODES["ontology_bridge"]:-null}" "${STAGE_DURATIONS["ontology_bridge"]:-null}" \
    "$overall_exit" <<'PYEOF'
import json, sys, os, hashlib
from datetime import datetime, timezone
(receipt_file, git_head, git_status_clean, report_dir,
 source_map, taxonomy_commits, taxonomy_paths, taxonomy_numstat,
 taxonomy_labels, taxonomy_habitats, phylogeny_json, dashboard_html,
 bridge_jsonl, bridge_edges_jsonl, bridge_report, bridge_relationship_report,
 lean_ec, lean_dur, tax_ec, tax_dur, source_ec, source_dur,
 extraction_ec, extraction_dur, weak_taxonomy_ec, weak_taxonomy_dur,
 habitats_ec, habitats_dur, phylo_ec, phylo_dur,
 dash_ec, dash_dur, bridge_ec, bridge_dur, overall_exit) = sys.argv[1:]

def sha256_file(path):
    if path and os.path.isfile(path):
        digest = hashlib.sha256()
        with open(path, 'rb') as f:
            for block in iter(lambda: f.read(1024 * 1024), b''):
                digest.update(block)
        return digest.hexdigest()
    return "absent"

receipt = {
    "schema": "info_geometry.pipeline_run_receipt.v2",
    "generated_at": datetime.now(timezone.utc).isoformat().replace('+00:00', 'Z'),
    "git_head": git_head,
    "git_status_clean": git_status_clean == 'true',
    "report_dir": report_dir,
    "stages": {
        "lean_build": {"exit_code": lean_ec if lean_ec in ('skipped', 'null', None) else int(lean_ec),
                       "duration_seconds": int(lean_dur) if lean_dur and lean_dur not in ('skipped', 'null', None) else None},
        "taxonomy_tests": {"exit_code": int(tax_ec) if tax_ec and tax_ec != 'null' else None,
                           "duration_seconds": int(tax_dur) if tax_dur and tax_dur != 'null' else None},
        "source_ontology": {"exit_code": int(source_ec) if source_ec and source_ec != 'null' else None,
                             "duration_seconds": int(source_dur) if source_dur and source_dur != 'null' else None},
        "commit_path_extraction": {"exit_code": int(extraction_ec) if extraction_ec and extraction_ec != 'null' else None,
                                    "duration_seconds": int(extraction_dur) if extraction_dur and extraction_dur != 'null' else None},
        "weak_commit_taxonomy": {"exit_code": int(weak_taxonomy_ec) if weak_taxonomy_ec and weak_taxonomy_ec != 'null' else None,
                                  "duration_seconds": int(weak_taxonomy_dur) if weak_taxonomy_dur and weak_taxonomy_dur != 'null' else None},
        "path_habitats": {"exit_code": int(habitats_ec) if habitats_ec and habitats_ec != 'null' else None,
                           "duration_seconds": int(habitats_dur) if habitats_dur and habitats_dur != 'null' else None},
        "phylogeny_export": {"exit_code": int(phylo_ec) if phylo_ec and phylo_ec != 'null' else None,
                             "duration_seconds": int(phylo_dur) if phylo_dur and phylo_dur != 'null' else None},
        "dashboard": {"exit_code": int(dash_ec) if dash_ec and dash_ec != 'null' else None,
                      "duration_seconds": int(dash_dur) if dash_dur and dash_dur != 'null' else None},
        "ontology_bridge": {"exit_code": int(bridge_ec) if bridge_ec and bridge_ec != 'null' else None,
                            "duration_seconds": int(bridge_dur) if bridge_dur and bridge_dur != 'null' else None},
    },
    "artifacts": {
        "source_ontology_map": source_map,
        "taxonomy_commits": taxonomy_commits,
        "taxonomy_paths": taxonomy_paths,
        "taxonomy_numstat": taxonomy_numstat,
        "weak_commit_labels": taxonomy_labels,
        "path_habitats": taxonomy_habitats,
        "phylogeny_export": phylogeny_json,
        "dashboard_html": dashboard_html,
        "bridge_jsonl": bridge_jsonl,
        "bridge_edges_jsonl": bridge_edges_jsonl,
        "bridge_report": bridge_report,
        "bridge_relationship_report": bridge_relationship_report,
    },
    "artifact_digests": {
        "source_ontology_map": sha256_file(source_map),
        "taxonomy_commits": sha256_file(taxonomy_commits),
        "taxonomy_paths": sha256_file(taxonomy_paths),
        "taxonomy_numstat": sha256_file(taxonomy_numstat),
        "weak_commit_labels": sha256_file(taxonomy_labels),
        "path_habitats": sha256_file(taxonomy_habitats),
        "phylogeny_export": sha256_file(phylogeny_json),
        "dashboard_html": sha256_file(dashboard_html),
        "bridge_jsonl": sha256_file(bridge_jsonl),
        "bridge_edges_jsonl": sha256_file(bridge_edges_jsonl),
        "bridge_report": sha256_file(bridge_report),
        "bridge_relationship_report": sha256_file(bridge_relationship_report),
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
