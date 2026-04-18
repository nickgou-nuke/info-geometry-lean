#!/usr/bin/env python3
"""
Hard integrity gate for closure/spectral/sinkhorn frontier clusters.

Enforced conditions on configured frontier files:
- no `sorry` / `admit`
- no `axiom` declarations
- no `postulate` declarations
"""

from __future__ import annotations

import argparse
import json
import re
import sys
from dataclasses import dataclass
from pathlib import Path
from typing import Any

ROOT = Path(__file__).resolve().parents[2]
DEFAULT_CONFIG = ROOT / "tools" / "quality" / "frontier_gate.json"


@dataclass(frozen=True)
class PatternRule:
    name: str
    regex: str
    compiled: re.Pattern[str]


@dataclass(frozen=True)
class Finding:
    cluster: str
    file: Path
    line: int
    rule: str
    snippet: str


def parse_args() -> argparse.Namespace:
    parser = argparse.ArgumentParser(
        description=(
            "Fail if configured frontier files contain forbidden placeholder/"
            "axiom tokens."
        )
    )
    parser.add_argument(
        "--config",
        type=Path,
        default=DEFAULT_CONFIG,
        help="Frontier gate JSON config path.",
    )
    parser.add_argument(
        "--json-out",
        type=Path,
        default=None,
        help="Optional JSON report output path.",
    )
    parser.add_argument(
        "--print-targets",
        action="store_true",
        help="Print unique configured build targets and exit.",
    )
    return parser.parse_args()


def load_config(path: Path) -> dict[str, Any]:
    try:
        data = json.loads(path.read_text(encoding="utf-8"))
    except Exception as ex:  # pragma: no cover - guardrail path
        raise SystemExit(f"[frontier-gate] failed reading config {path}: {ex}") from ex
    if not isinstance(data, dict):
        raise SystemExit(f"[frontier-gate] expected object JSON at {path}")
    return data


def parse_rules(cfg: dict[str, Any]) -> list[PatternRule]:
    raw_rules = cfg.get("forbidden_patterns")
    if not isinstance(raw_rules, list) or not raw_rules:
        raise SystemExit("[frontier-gate] config missing non-empty `forbidden_patterns` list")
    rules: list[PatternRule] = []
    for row in raw_rules:
        if not isinstance(row, dict):
            raise SystemExit("[frontier-gate] every forbidden pattern row must be an object")
        name = row.get("name")
        regex = row.get("regex")
        if not isinstance(name, str) or not isinstance(regex, str):
            raise SystemExit("[frontier-gate] each forbidden pattern needs string `name` and `regex`")
        rules.append(PatternRule(name=name, regex=regex, compiled=re.compile(regex)))
    return rules


def iter_cluster_files(cfg: dict[str, Any]) -> list[tuple[str, Path]]:
    clusters = cfg.get("clusters")
    if not isinstance(clusters, dict) or not clusters:
        raise SystemExit("[frontier-gate] config missing non-empty `clusters` object")
    out: list[tuple[str, Path]] = []
    for cluster_name, payload in clusters.items():
        if not isinstance(payload, dict):
            raise SystemExit(f"[frontier-gate] cluster `{cluster_name}` must be an object")
        files = payload.get("files")
        if not isinstance(files, list) or not files:
            raise SystemExit(f"[frontier-gate] cluster `{cluster_name}` requires non-empty `files` list")
        for rel in files:
            if not isinstance(rel, str):
                raise SystemExit(f"[frontier-gate] cluster `{cluster_name}` has non-string file path")
            out.append((cluster_name, ROOT / rel))
    return out


def unique_build_targets(cfg: dict[str, Any]) -> list[str]:
    clusters = cfg.get("clusters", {})
    if not isinstance(clusters, dict):
        return []
    seen: set[str] = set()
    ordered: list[str] = []
    for payload in clusters.values():
        if not isinstance(payload, dict):
            continue
        targets = payload.get("buildTargets", [])
        if not isinstance(targets, list):
            continue
        for t in targets:
            if isinstance(t, str) and t not in seen:
                seen.add(t)
                ordered.append(t)
    return ordered


def line_for_offset(text: str, idx: int) -> int:
    return text.count("\n", 0, idx) + 1


def scan_files(
    cluster_files: list[tuple[str, Path]], rules: list[PatternRule]
) -> tuple[list[Finding], list[tuple[str, Path]]]:
    findings: list[Finding] = []
    missing: list[tuple[str, Path]] = []
    for cluster_name, path in cluster_files:
        if not path.exists():
            missing.append((cluster_name, path))
            continue
        text = path.read_text(encoding="utf-8")
        for rule in rules:
            for m in rule.compiled.finditer(text):
                line = line_for_offset(text, m.start())
                snippet = text.splitlines()[line - 1].strip()
                findings.append(
                    Finding(
                        cluster=cluster_name,
                        file=path,
                        line=line,
                        rule=rule.name,
                        snippet=snippet,
                    )
                )
    return findings, missing


def main() -> int:
    args = parse_args()
    cfg = load_config(args.config)

    if args.print_targets:
        for target in unique_build_targets(cfg):
            print(target)
        return 0

    rules = parse_rules(cfg)
    cluster_files = iter_cluster_files(cfg)
    findings, missing = scan_files(cluster_files, rules)

    print("[frontier-gate] scanning configured frontier clusters")
    print(f"[frontier-gate] files={len(cluster_files)} rules={len(rules)}")

    if missing:
        print("[frontier-gate] missing configured files:")
        for cluster, path in missing:
            print(f"  - [{cluster}] {path.relative_to(ROOT)}")

    if findings:
        print("[frontier-gate] forbidden tokens detected:")
        for f in findings:
            rel = f.file.relative_to(ROOT)
            print(f"  - [{f.cluster}] {rel}:{f.line} [{f.rule}] {f.snippet}")
    else:
        print("[frontier-gate] no forbidden tokens found")

    status = 0 if (not missing and not findings) else 1
    print("[frontier-gate] PASSED" if status == 0 else "[frontier-gate] FAILED")

    if args.json_out is not None:
        payload = {
            "config": str(args.config),
            "status": "passed" if status == 0 else "failed",
            "missing": [
                {"cluster": cluster, "file": str(path.relative_to(ROOT))}
                for cluster, path in missing
            ],
            "findings": [
                {
                    "cluster": f.cluster,
                    "file": str(f.file.relative_to(ROOT)),
                    "line": f.line,
                    "rule": f.rule,
                    "snippet": f.snippet,
                }
                for f in findings
            ],
            "build_targets": unique_build_targets(cfg),
        }
        args.json_out.parent.mkdir(parents=True, exist_ok=True)
        args.json_out.write_text(json.dumps(payload, indent=2) + "\n", encoding="utf-8")
        print(f"[frontier-gate] wrote report: {args.json_out}")

    return status


if __name__ == "__main__":
    sys.exit(main())
