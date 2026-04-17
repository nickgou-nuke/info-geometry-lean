#!/usr/bin/env python3
from __future__ import annotations

import argparse
import hashlib
import json
import re
from datetime import datetime, timedelta, timezone
from pathlib import Path
from typing import Any, Iterable


def _utc_now() -> datetime:
    return datetime.now(timezone.utc)


def _utc_iso(dt: datetime) -> str:
    return dt.astimezone(timezone.utc).isoformat()


def _iter_jsonl(path: Path) -> Iterable[dict[str, Any]]:
    if not path.exists():
        return
    with path.open("r", encoding="utf-8") as handle:
        for line in handle:
            s = line.strip()
            if not s:
                continue
            try:
                obj = json.loads(s)
            except Exception:
                continue
            if isinstance(obj, dict):
                yield obj


def _norm_file(path_text: str, repo_root: Path) -> str:
    p = Path(path_text)
    if p.is_absolute():
        return str(p.resolve())
    return str((repo_root / p).resolve())


def _load_decl_index(
    decls_path: Path,
    repo_root: Path,
) -> tuple[set[str], dict[str, list[tuple[int, str]]]]:
    names: set[str] = set()
    by_file: dict[str, list[tuple[int, str]]] = {}
    for row in _iter_jsonl(decls_path):
        name = str(row.get("name", "")).strip()
        file_raw = row.get("file")
        line_raw = row.get("line")
        if not name:
            continue
        names.add(name)
        if isinstance(file_raw, str) and file_raw.strip() and isinstance(line_raw, int):
            file_key = _norm_file(file_raw.strip(), repo_root)
            by_file.setdefault(file_key, []).append((line_raw, name))
    for file_key, rows in by_file.items():
        rows.sort(key=lambda x: x[0])
        by_file[file_key] = rows
    return names, by_file


def _closest_decl(file_rows: list[tuple[int, str]], line: int) -> str | None:
    if not file_rows:
        return None
    best: tuple[int, str] | None = None
    for decl_line, decl_name in file_rows:
        if decl_line <= line:
            best = (decl_line, decl_name)
        else:
            break
    if best is not None:
        return best[1]
    return min(file_rows, key=lambda row: abs(row[0] - line))[1]


_LOG_LOC_RE = re.compile(
    r"^(?P<file>.+?\.lean):(?P<line>\d+):(?P<col>\d+):\s*(?P<sev>error|warning):\s*(?P<msg>.*)$"
)
_DECL_TOKEN_RE = re.compile(r"\b([A-Z][A-Za-z0-9_']*(?:\.[A-Za-z0-9_']+)+)\b")


def _classify_error_kind(msg: str) -> str:
    s = msg.strip().lower()
    if not s:
        return "unknown"
    if "failed to synthesize" in s:
        return "failedToSynthesize"
    if "type mismatch" in s:
        return "typeMismatch"
    if "unknown constant" in s:
        return "unknownConstant"
    if "invalid field" in s:
        return "invalidField"
    if "unsolved goals" in s or "tactic" in s:
        return "tacticFailure"
    if "warning" in s:
        return "warning"
    head = re.split(r"[^a-z0-9]+", s)[0]
    return head or "unknown"


def _extract_decl_mentions(msg: str, known_names: set[str]) -> list[str]:
    out: list[str] = []
    seen: set[str] = set()
    for m in _DECL_TOKEN_RE.finditer(msg):
        token = m.group(1)
        if token in known_names and token not in seen:
            seen.add(token)
            out.append(token)
    return out


def _load_edge_kind_index(path: Path) -> dict[tuple[str, str], str]:
    by_pair: dict[tuple[str, str], str] = {}
    for row in _iter_jsonl(path):
        src = str(row.get("src", "")).strip()
        dst = str(row.get("dst", "")).strip()
        raw_kind = str(row.get("kind", "")).strip().lower()
        if not src or not dst:
            continue
        kind = "depends_type" if raw_kind == "type" else "depends_value"
        key = (src, dst)
        current = by_pair.get(key)
        if current == "depends_type":
            continue
        by_pair[key] = kind
    return by_pair


def _failure_id(src: str, dst: str, kind: str, error_kind: str) -> str:
    digest = hashlib.sha1(f"{src}|{dst}|{kind}|{error_kind}".encode("utf-8")).hexdigest()
    return f"ft_{digest[:24]}"


def _record_from_existing(row: dict[str, Any]) -> dict[str, Any] | None:
    src = str(row.get("src", "")).strip()
    dst = str(row.get("dst", "")).strip()
    kind = str(row.get("kind", "")).strip() or "depends_value"
    error_kind = str(row.get("error_kind", "")).strip() or "unknown"
    if not src or not dst:
        return None
    count_raw = row.get("count")
    count = int(count_raw) if isinstance(count_raw, int) and count_raw > 0 else 1
    total_cost_raw = row.get("total_cost")
    total_cost = int(total_cost_raw) if isinstance(total_cost_raw, int) and total_cost_raw >= 0 else 0
    witnesses = row.get("witnesses")
    if not isinstance(witnesses, list):
        witnesses = []
    return {
        "id": str(row.get("id", "")).strip() or _failure_id(src, dst, kind, error_kind),
        "state": "failed",
        "src": src,
        "dst": dst,
        "kind": kind,
        "error_kind": error_kind,
        "count": count,
        "total_cost": total_cost,
        "witnesses": [str(w).strip() for w in witnesses if str(w).strip()],
        "first_seen": str(row.get("first_seen", "")).strip() or _utc_iso(_utc_now()),
        "last_seen": str(row.get("last_seen", "")).strip() or _utc_iso(_utc_now()),
        "cooldown_until": str(row.get("cooldown_until", "")).strip() or _utc_iso(_utc_now()),
    }


def _merge_failure(
    acc: dict[tuple[str, str, str, str], dict[str, Any]],
    *,
    src: str,
    dst: str,
    kind: str,
    error_kind: str,
    witness: str,
    cost: int,
    cooldown_hours: int,
) -> None:
    now = _utc_now()
    key = (src, dst, kind, error_kind)
    row = acc.get(key)
    if row is None:
        row = {
            "id": _failure_id(src, dst, kind, error_kind),
            "state": "failed",
            "src": src,
            "dst": dst,
            "kind": kind,
            "error_kind": error_kind,
            "count": 0,
            "total_cost": 0,
            "witnesses": [],
            "first_seen": _utc_iso(now),
            "last_seen": _utc_iso(now),
            "cooldown_until": _utc_iso(now + timedelta(hours=cooldown_hours)),
        }
        acc[key] = row

    row["count"] = int(row.get("count", 0)) + 1
    row["total_cost"] = int(row.get("total_cost", 0)) + max(0, int(cost))
    row["last_seen"] = _utc_iso(now)
    row["cooldown_until"] = _utc_iso(now + timedelta(hours=cooldown_hours))
    if witness and witness not in row["witnesses"]:
        row["witnesses"].append(witness)


def run_failure_harvest(
    *,
    repo_root: Path,
    defects_path: Path,
    output_path: Path,
    dag_edges_path: Path,
    decls_path: Path,
    build_logs: list[Path],
    include_warnings: bool,
    log_max_events: int,
    cooldown_hours: int,
    max_witnesses: int,
    merge_existing: bool,
) -> dict[str, Any]:
    known_decl_names, decls_by_file = _load_decl_index(decls_path, repo_root)
    edge_kind_by_pair = _load_edge_kind_index(dag_edges_path)
    failures: dict[tuple[str, str, str, str], dict[str, Any]] = {}

    if merge_existing and output_path.exists():
        for row in _iter_jsonl(output_path):
            parsed = _record_from_existing(row)
            if parsed is None:
                continue
            key = (
                parsed["src"],
                parsed["dst"],
                parsed["kind"],
                parsed["error_kind"],
            )
            failures[key] = parsed

    source_rows = 0
    log_events = 0
    for row in _iter_jsonl(defects_path):
        source_rows += 1
        src = str(row.get("src", "")).strip()
        dst = str(row.get("dst", "")).strip()
        if not src or not dst:
            continue
        defect = row.get("defect") if isinstance(row.get("defect"), dict) else {}
        error_kind = str(defect.get("kind", "")).strip() or "unknown"
        witness = str(defect.get("witness", "")).strip()
        cost_raw = defect.get("cost")
        cost = int(cost_raw) if isinstance(cost_raw, int) and cost_raw >= 0 else 0

        kind = edge_kind_by_pair.get((src, dst), "depends_value")
        _merge_failure(
            failures,
            src=src,
            dst=dst,
            kind=kind,
            error_kind=error_kind,
            witness=witness,
            cost=cost,
            cooldown_hours=cooldown_hours,
        )

    for log_path in build_logs:
        if log_max_events > 0 and log_events >= log_max_events:
            break
        if not log_path.exists():
            continue
        with log_path.open("r", encoding="utf-8", errors="replace") as handle:
            for line in handle:
                if log_max_events > 0 and log_events >= log_max_events:
                    break
                m = _LOG_LOC_RE.match(line.strip())
                if m is None:
                    continue
                sev = str(m.group("sev")).strip().lower()
                if sev == "warning" and not include_warnings:
                    continue

                file_key = _norm_file(m.group("file"), repo_root)
                line_no = int(m.group("line"))
                msg = m.group("msg")
                src = _closest_decl(decls_by_file.get(file_key, []), line_no)
                if not src:
                    continue

                error_kind = _classify_error_kind(msg)
                mentions = [name for name in _extract_decl_mentions(msg, known_decl_names) if name != src]
                witness = msg[:220].strip()
                cost = 1 if sev == "warning" else 2

                if mentions:
                    for dst in mentions:
                        kind = edge_kind_by_pair.get((src, dst), "depends_value")
                        _merge_failure(
                            failures,
                            src=src,
                            dst=dst,
                            kind=kind,
                            error_kind=error_kind,
                            witness=witness,
                            cost=cost,
                            cooldown_hours=cooldown_hours,
                        )
                else:
                    # Keep unbound failures as self transitions so the event is retained
                    # even when no destination declaration can be recovered from the log.
                    kind = edge_kind_by_pair.get((src, src), "depends_value")
                    _merge_failure(
                        failures,
                        src=src,
                        dst=src,
                        kind=kind,
                        error_kind=error_kind,
                        witness=witness,
                        cost=cost,
                        cooldown_hours=cooldown_hours,
                    )
                log_events += 1

    rows = sorted(
        failures.values(),
        key=lambda r: (-int(r.get("count", 0)), str(r.get("src", "")), str(r.get("dst", ""))),
    )
    for row in rows:
        witnesses = row.get("witnesses")
        if isinstance(witnesses, list):
            row["witnesses"] = witnesses[:max_witnesses]

    output_path.parent.mkdir(parents=True, exist_ok=True)
    with output_path.open("w", encoding="utf-8") as handle:
        for row in rows:
            handle.write(json.dumps(row, ensure_ascii=True) + "\n")

    return {
        "created_at": _utc_iso(_utc_now()),
        "source_defects": str(defects_path),
        "source_logs": [str(p) for p in build_logs],
        "output": str(output_path),
        "rows_scanned": source_rows,
        "log_events": log_events,
        "failed_transitions": len(rows),
    }


def _parse_args() -> argparse.Namespace:
    parser = argparse.ArgumentParser(
        description="Harvest process-flow defects into LeanTrail failed transition memory."
    )
    parser.add_argument(
        "--defects",
        default="artifacts/dag/process-flow/defects.jsonl",
        help="Input defects JSONL from process-flow export.",
    )
    parser.add_argument(
        "--dag-edges",
        default="artifacts/dag/index/edges.jsonl",
        help="DAG edges JSONL used to infer edge kind (type/value).",
    )
    parser.add_argument(
        "--decls",
        default="artifacts/dag/index/decls.jsonl",
        help="Declaration index JSONL used to map build-log locations to declarations.",
    )
    parser.add_argument(
        "--build-log",
        action="append",
        default=[],
        help="Optional build/strict log file to mine (repeatable).",
    )
    parser.add_argument(
        "--build-stdout",
        default=None,
        help="Optional alias for a build stdout log file.",
    )
    parser.add_argument(
        "--build-stderr",
        default=None,
        help="Optional alias for a build stderr log file.",
    )
    parser.add_argument(
        "--include-warnings",
        action="store_true",
        help="Include warning lines from build logs (default: errors only).",
    )
    parser.add_argument(
        "--log-max-events",
        type=int,
        default=20000,
        help="Maximum parsed log events (0 means unlimited).",
    )
    parser.add_argument(
        "--out",
        default="artifacts/leantrail/failed_transitions.jsonl",
        help="Output failed transitions JSONL.",
    )
    parser.add_argument(
        "--cooldown-hours",
        type=int,
        default=24,
        help="Retry cooldown window for failed transitions.",
    )
    parser.add_argument(
        "--max-witnesses",
        type=int,
        default=8,
        help="Cap witness strings retained per failure edge.",
    )
    parser.add_argument(
        "--merge-existing",
        action="store_true",
        help="Merge with existing output file if present.",
    )
    parser.add_argument(
        "--json-out",
        default="artifacts/leantrail/failure_harvest_report.json",
        help="Write compact report JSON.",
    )
    return parser.parse_args()


def main() -> int:
    args = _parse_args()
    repo_root = Path(".").resolve()
    logs: list[Path] = []
    for raw in list(args.build_log or []):
        text = str(raw).strip()
        if text:
            logs.append(Path(text).resolve())
    for raw in [args.build_stdout, args.build_stderr]:
        text = str(raw).strip() if raw is not None else ""
        if text:
            logs.append(Path(text).resolve())
    # stable unique
    seen: set[str] = set()
    uniq_logs: list[Path] = []
    for p in logs:
        key = str(p)
        if key not in seen:
            seen.add(key)
            uniq_logs.append(p)

    report = run_failure_harvest(
        repo_root=repo_root,
        defects_path=Path(args.defects).resolve(),
        output_path=Path(args.out).resolve(),
        dag_edges_path=Path(args.dag_edges).resolve(),
        decls_path=Path(args.decls).resolve(),
        build_logs=uniq_logs,
        include_warnings=bool(args.include_warnings),
        log_max_events=max(0, int(args.log_max_events)),
        cooldown_hours=max(0, int(args.cooldown_hours)),
        max_witnesses=max(1, int(args.max_witnesses)),
        merge_existing=bool(args.merge_existing),
    )

    json_out = Path(args.json_out).resolve()
    json_out.parent.mkdir(parents=True, exist_ok=True)
    json_out.write_text(json.dumps(report, indent=2, ensure_ascii=True) + "\n", encoding="utf-8")
    print(
        "Failure harvest written:",
        report["output"],
        f"(rows={report['failed_transitions']}, defects={report['rows_scanned']}, logs={report['log_events']})",
    )
    print(f"Report written: {json_out}")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
