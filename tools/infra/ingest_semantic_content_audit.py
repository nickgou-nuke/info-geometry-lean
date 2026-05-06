#!/usr/bin/env python3
from __future__ import annotations

import argparse
import hashlib
import json
import sys
from datetime import datetime, timezone
from pathlib import Path
from typing import Any, Iterable

if __package__ in (None, ""):
    _ROOT = Path(__file__).resolve().parents[2]
    sys.path.insert(0, str(_ROOT))
    from tools.infra.arango_env import arango_database, arango_endpoint, arango_password, arango_username, load_repo_arango_env
    from tools.pathing import repo_root
else:
    from tools.infra.arango_env import arango_database, arango_endpoint, arango_password, arango_username, load_repo_arango_env
    from tools.pathing import repo_root


SCHEMA_RUN = "info_geometry.semantic_content_audit.run.v1"
SCHEMA_MODULE = "info_geometry.semantic_content_audit.module.v1"
SCHEMA_FINDING = "info_geometry.semantic_content_audit.finding.v1"
SCHEMA_IMPORTER_EDGE = "info_geometry.semantic_content_audit.importer_edge.v1"
SCHEMA_HIVE_TASK = "info_geometry.hive_task.v1"

SEMANTIC_SEVERITY = {
    "quarantine_manifest_inconsistency": 105.0,
    "proof_hole_blocker": 100.0,
    "explicit_axiom_blocker": 95.0,
    "vacuous_or_surrogate_surface": 80.0,
    "constructivity_review_surface": 50.0,
    "review_scaffold_surface": 30.0,
    "manifested_quarantine_no_current_findings": 10.0,
    "content_clean_by_this_audit": 0.0,
}

TASK_KIND_BY_STATUS = {
    "proof_hole_blocker": "constructivity.repair.proof_hole",
    "explicit_axiom_blocker": "constructivity.repair.axiom",
    "vacuous_or_surrogate_surface": "constructivity.repair.vacuous",
    "quarantine_manifest_inconsistency": "constructivity.repair.manifest",
    "constructivity_review_surface": "constructivity.review.constructivity",
    "review_scaffold_surface": "constructivity.review.scaffold",
}

STATUS_ORDER = [
    "quarantine_manifest_inconsistency",
    "proof_hole_blocker",
    "explicit_axiom_blocker",
    "vacuous_or_surrogate_surface",
    "review_scaffold_surface",
    "manifested_quarantine_no_current_findings",
    "constructivity_review_surface",
    "content_clean_by_this_audit",
]
STATUS_RANK = {status: index for index, status in enumerate(STATUS_ORDER)}


def utc_stamp() -> str:
    return datetime.now(timezone.utc).strftime("%Y%m%dT%H%M%SZ")


def stable_key(*parts: Any) -> str:
    raw = "|".join(str(part) for part in parts)
    return hashlib.sha256(raw.encode("utf-8")).hexdigest()[:40]


def file_digest(path: Path) -> str:
    return hashlib.sha256(path.read_bytes()).hexdigest()[:40]


def read_json(path: Path) -> dict[str, Any]:
    return json.loads(path.read_text(encoding="utf-8"))


def iter_jsonl(path: Path) -> Iterable[dict[str, Any]]:
    if not path.exists():
        return
    with path.open("r", encoding="utf-8") as handle:
        for line in handle:
            line = line.strip()
            if line:
                row = json.loads(line)
                if isinstance(row, dict):
                    yield row


def write_jsonl(path: Path, rows: Iterable[dict[str, Any]]) -> int:
    path.parent.mkdir(parents=True, exist_ok=True)
    count = 0
    with path.open("w", encoding="utf-8") as handle:
        for row in rows:
            handle.write(json.dumps(row, sort_keys=True) + "\n")
            count += 1
    return count


def load_graph_index(nodes_path: Path, edges_path: Path) -> dict[str, Any]:
    nodes_by_name: dict[str, dict[str, Any]] = {}
    decls_by_module: dict[str, list[str]] = {}
    reverse_dependents: dict[str, set[str]] = {}

    for row in iter_jsonl(nodes_path):
        name = row.get("name") or row.get("decl")
        if not isinstance(name, str) or not name:
            continue
        nodes_by_name[name] = row
        module = row.get("module")
        if isinstance(module, str) and module:
            decls_by_module.setdefault(module, []).append(name)

    for row in iter_jsonl(edges_path):
        src = row.get("src")
        dst = row.get("dst")
        if isinstance(src, str) and isinstance(dst, str):
            reverse_dependents.setdefault(dst, set()).add(src)

    return {
        "nodes_by_name": nodes_by_name,
        "decls_by_module": decls_by_module,
        "reverse_dependents": reverse_dependents,
    }


def module_decl_names(module: str, graph: dict[str, Any]) -> list[str]:
    exact = list(graph["decls_by_module"].get(module, []))
    if exact:
        return sorted(exact)
    prefix = module + "."
    return sorted(name for name in graph["nodes_by_name"] if name.startswith(prefix))


def graph_context(
    module: dict[str, Any],
    graph: dict[str, Any],
    *,
    enclosing_decl: str | None = None,
    max_decl_sample: int = 20,
) -> dict[str, Any]:
    if enclosing_decl and enclosing_decl in graph["nodes_by_name"]:
        names = [enclosing_decl]
    else:
        names = module_decl_names(str(module.get("module", "")), graph)
    rev: set[str] = set()
    for name in names:
        rev.update(graph["reverse_dependents"].get(name, set()))
    return {
        "candidate_decl_count": len(names),
        "candidate_decl_sample": names[:max_decl_sample],
        "graph_reverse_dependent_count": len(rev),
        "graph_reverse_dependent_sample": sorted(rev)[:max_decl_sample],
        "graph_capstone_dependent_count": None,
        "graph_dominator_count": None,
        "graph_overlay_authority": "not computed by offline JSONL ingest; use Arango overlays for SCC/capstone/dominator scheduling",
        "graph_context_authority": "navigation only; not proof authority",
    }


def source_excerpt_for_module(module: dict[str, Any], finding: dict[str, Any]) -> str:
    line = finding.get("line")
    for excerpt in module.get("source_excerpts", []):
        if excerpt.get("line") == line:
            return str(excerpt.get("text", ""))
    excerpts = module.get("source_excerpts", [])
    if excerpts:
        return str(excerpts[0].get("text", ""))
    return ""


def priority_for(module: dict[str, Any], gctx: dict[str, Any]) -> float:
    status = str(module.get("semantic_status", ""))
    severity = SEMANTIC_SEVERITY.get(status, 0.0)
    direct_importers = float(module.get("direct_importer_count") or 0)
    forbidden_importers = float(module.get("forbidden_importer_count") or 0)
    reverse = float(gctx.get("graph_reverse_dependent_count") or 0)
    return round(severity + 2.0 * direct_importers + 5.0 * forbidden_importers + min(reverse, 200.0) * 0.25, 3)


def status_allowed(status: str, min_status: str | None) -> bool:
    if not min_status:
        return True
    try:
        return STATUS_RANK[status] <= STATUS_RANK[min_status]
    except KeyError:
        return False


def enclosing_decl_name(finding: dict[str, Any]) -> str:
    enclosing = finding.get("enclosing_decl")
    if isinstance(enclosing, dict):
        decl = enclosing.get("decl")
        return str(decl) if decl else ""
    if isinstance(enclosing, str):
        return enclosing
    return ""


def enclosing_decl_object(finding: dict[str, Any]) -> dict[str, Any] | None:
    enclosing = finding.get("enclosing_decl")
    if isinstance(enclosing, dict):
        decl = enclosing.get("decl")
        if not decl:
            return None
        return {
            "decl": decl,
            "kind": enclosing.get("kind"),
            "line": enclosing.get("line"),
            "local_name": enclosing.get("local_name"),
        }
    decl = enclosing_decl_name(finding)
    if not decl:
        return None
    return {
        "decl": decl,
        "kind": finding.get("enclosing_decl_kind"),
        "line": finding.get("enclosing_decl_line"),
        "local_name": finding.get("enclosing_decl_raw_name"),
    }


def finding_key_for(module: dict[str, Any], finding: dict[str, Any]) -> str:
    path = finding.get("path") or module.get("path") or ""
    return stable_key(
        SCHEMA_FINDING,
        path,
        finding.get("line"),
        finding.get("category"),
        enclosing_decl_name(finding),
        finding.get("detail"),
    )


def task_key_for(finding_key: str, min_status: str | None, target_decl: str) -> str:
    return stable_key("semantic_content_repair", finding_key, min_status or "", target_decl)


def build_rows(
    report: dict[str, Any],
    graph: dict[str, Any],
    *,
    run_key: str,
    min_status: str | None = None,
) -> dict[str, list[dict[str, Any]]]:
    now = datetime.now(timezone.utc).isoformat()
    run_doc = {
        "_key": run_key,
        "schema": SCHEMA_RUN,
        "created_at": now,
        "source_schema": report.get("schema"),
        "summary": report.get("summary", {}),
        "status_rank": STATUS_RANK,
        "authority": {
            "semantic_audit_is_triage": True,
            "graph_context_is_navigation_only": True,
            "lean_remains_proof_authority": True,
        },
    }

    modules: list[dict[str, Any]] = []
    findings: list[dict[str, Any]] = []
    importer_edges: list[dict[str, Any]] = []
    tasks: list[dict[str, Any]] = []

    for module in report.get("modules", []):
        if not isinstance(module, dict):
            continue
        module_name = str(module.get("module", ""))
        module_key = stable_key("module", run_key, module_name)
        gctx = graph_context(module, graph)
        priority = priority_for(module, gctx)
        module_doc = {
            "_key": module_key,
            "schema": SCHEMA_MODULE,
            "run_key": run_key,
            "module": module_name,
            "path": module.get("path"),
            "semantic_status": module.get("semantic_status"),
            "recommended_action": module.get("recommended_action"),
            "current_manifest_reason": module.get("current_manifest_reason"),
            "finding_categories": module.get("finding_categories", []),
            "direct_importer_count": module.get("direct_importer_count", 0),
            "forbidden_importer_count": module.get("forbidden_importer_count", 0),
            "importer_class_counts": module.get("importer_class_counts", {}),
            "priority": priority,
            "graph_context": gctx,
            "authority": "diagnostic",
        }
        modules.append(module_doc)

        for importer in module.get("direct_importers", []):
            edge_key = stable_key("importer", run_key, module_name, importer)
            importer_edges.append(
                {
                    "_key": edge_key,
                    "_from": f"semantic_content_audit_modules/{module_key}",
                    "_to": f"semantic_content_audit_modules/{stable_key('module', run_key, importer)}",
                    "schema": SCHEMA_IMPORTER_EDGE,
                    "run_key": run_key,
                    "module": module_name,
                    "importer": importer,
                    "importer_class": (
                        module.get("importer_class_counts", {})
                    ),
                    "authority": "direct source import only",
                }
            )

        module_findings = module.get("findings") or []
        if not module_findings and module.get("semantic_status") == "manifested_quarantine_no_current_findings":
            continue

        for finding in module_findings:
            if not isinstance(finding, dict):
                continue
            finding_key = finding_key_for(module, finding)
            source_excerpt = source_excerpt_for_module(module, finding)
            enclosing_decl = enclosing_decl_name(finding)
            enclosing_decl_payload = enclosing_decl_object(finding)
            finding_gctx = graph_context(
                module,
                graph,
                enclosing_decl=enclosing_decl or None,
            )
            status = str(module.get("semantic_status", ""))
            finding_doc = {
                "_key": finding_key,
                "schema": SCHEMA_FINDING,
                "run_key": run_key,
                "module_key": module_key,
                "module": module_name,
                "path": finding.get("path") or module.get("path"),
                "line": finding.get("line"),
                "category": finding.get("category"),
                "detail": finding.get("detail"),
                "enclosing_decl": enclosing_decl_payload,
                "enclosing_decl_name": enclosing_decl or None,
                "enclosing_decl_kind": finding.get("enclosing_decl_kind"),
                "enclosing_decl_line": finding.get("enclosing_decl_line"),
                "semantic_status": status,
                "status_rank": STATUS_RANK.get(status),
                "recommended_action": module.get("recommended_action"),
                "current_manifest_reason": module.get("current_manifest_reason"),
                "source_excerpt": source_excerpt,
                "priority": priority_for(module, finding_gctx),
                "graph_context": finding_gctx,
                "authority": "source_diagnostic_not_proof",
            }
            findings.append(finding_doc)

            task_kind = TASK_KIND_BY_STATUS.get(status)
            if task_kind and status_allowed(status, min_status):
                target_decl = enclosing_decl or (
                    finding_gctx.get("candidate_decl_sample", [""])[0]
                    if finding_gctx.get("candidate_decl_sample")
                    else ""
                )
                task_key = task_key_for(finding_key, min_status, str(target_decl))
                task_priority = priority_for(module, finding_gctx)
                tasks.append(
                    {
                        "_key": task_key,
                        "schema": SCHEMA_HIVE_TASK,
                        "task_kind": task_kind,
                        "task_family": "semantic_content_repair",
                        "repair_route": task_kind,
                        "queue_name": "proof-search" if "repair" in task_kind else "audit-semantic",
                        "status": "pending",
                        "priority": task_priority,
                        "module": module_name,
                        "path": finding.get("path") or module.get("path"),
                        "file": finding.get("path") or module.get("path"),
                        "line": finding.get("line"),
                        "enclosing_decl": enclosing_decl_payload,
                        "target_decl": target_decl,
                        "enclosing_decl_kind": finding.get("enclosing_decl_kind"),
                        "finding_key": finding_key,
                        "category": finding.get("category"),
                        "finding_category": finding.get("category"),
                        "semantic_status": status,
                        "status_rank": STATUS_RANK.get(status),
                        "recommended_action": module.get("recommended_action"),
                        "source_excerpt": source_excerpt,
                        "direct_importer_count": module.get("direct_importer_count", 0),
                        "forbidden_importer_count": module.get("forbidden_importer_count", 0),
                        "candidate_decls": finding_gctx.get("candidate_decl_sample", []),
                        "graph_reverse_dependent_count": finding_gctx.get("graph_reverse_dependent_count", 0),
                        "created_by": "ingest_semantic_content_audit",
                        "created_at": now,
                        "authority": "source_diagnostic_not_proof",
                    }
                )

    return {
        "semantic_content_audit_runs": [run_doc],
        "semantic_content_audit_modules": modules,
        "semantic_content_audit_findings": findings,
        "semantic_content_audit_importer_edges": importer_edges,
        "hive_tasks": tasks,
    }


def import_rows_arango(
    endpoint: str,
    database: str,
    username: str,
    password: str,
    collection: str,
    rows: list[dict[str, Any]],
) -> None:
    if not rows:
        return
    from tools.alexandria.arango_ingest import ensure_collection, import_rows

    edge = collection.endswith("_edges") or collection == "semantic_content_audit_importer_edges"
    ensure_collection(endpoint, database, username, password, collection, edge=edge)
    import_rows(endpoint, database, username, password, collection, rows)


def main() -> int:
    load_repo_arango_env(Path.cwd())
    root = repo_root()
    parser = argparse.ArgumentParser(description="Ingest semantic content audit into graph/Hive scheduling artifacts.")
    parser.add_argument("--input", type=Path, default=root / "reports/dag/semantic-content-audit.json")
    parser.add_argument("--nodes", type=Path, default=root / "artifacts/dag/index/ig_nodes.jsonl")
    parser.add_argument("--edges", type=Path, default=root / "artifacts/dag/index/ig_edges.jsonl")
    parser.add_argument("--out-dir", type=Path, default=root / "reports/dag/semantic-content-audit-ingest")
    parser.add_argument("--json-out", type=Path, default=None, help="Optional extra path for the ingest summary JSON.")
    parser.add_argument(
        "--tasks-out",
        "--hive-tasks-out",
        dest="tasks_out",
        type=Path,
        default=root / "reports/dag/semantic-content-hive-tasks.jsonl",
    )
    parser.add_argument("--run-key", default="")
    parser.add_argument("--enqueue-hive-tasks", action="store_true")
    parser.add_argument(
        "--min-status",
        choices=STATUS_ORDER,
        default=None,
        help="Only emit Hive tasks for statuses at least this severe in the scheduler order.",
    )
    parser.add_argument("--write-arango", action="store_true")
    parser.add_argument("--endpoint", default=arango_endpoint())
    parser.add_argument("--database", default=arango_database("infogeometry"))
    parser.add_argument("--username", default=arango_username())
    parser.add_argument("--password", default=arango_password("alexandria_root"))
    args = parser.parse_args()

    report = read_json(args.input)
    run_key = args.run_key or f"semantic_audit_{file_digest(args.input)}"
    graph = load_graph_index(args.nodes, args.edges)
    rows_by_collection = build_rows(report, graph, run_key=run_key, min_status=args.min_status)

    args.out_dir.mkdir(parents=True, exist_ok=True)
    counts: dict[str, int] = {}
    for collection, rows in rows_by_collection.items():
        if collection == "hive_tasks" and not args.enqueue_hive_tasks:
            continue
        counts[collection] = write_jsonl(args.out_dir / f"{collection}.jsonl", rows)

    if args.enqueue_hive_tasks:
        counts["tasks_out"] = write_jsonl(args.tasks_out, rows_by_collection["hive_tasks"])

    if args.write_arango:
        for collection, rows in rows_by_collection.items():
            if collection == "hive_tasks" and not args.enqueue_hive_tasks:
                continue
            import_rows_arango(args.endpoint, args.database, args.username, args.password, collection, rows)

    summary = {
        "schema": "info_geometry.semantic_content_audit.ingest_summary.v1",
        "run_key": run_key,
        "input": str(args.input),
        "out_dir": str(args.out_dir),
        "wrote_arango": bool(args.write_arango),
        "enqueued_hive_tasks": bool(args.enqueue_hive_tasks),
        "database": args.database if args.write_arango else None,
        "status_rank": STATUS_RANK,
        "min_status": args.min_status,
        "counts": counts,
        "authority": "diagnostic scheduling only; Lean remains proof authority",
    }
    (args.out_dir / "summary.json").write_text(json.dumps(summary, indent=2, sort_keys=True) + "\n", encoding="utf-8")
    if args.json_out is not None:
        args.json_out.parent.mkdir(parents=True, exist_ok=True)
        args.json_out.write_text(json.dumps(summary, indent=2, sort_keys=True) + "\n", encoding="utf-8")
    print(json.dumps(summary, indent=2, sort_keys=True))
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
