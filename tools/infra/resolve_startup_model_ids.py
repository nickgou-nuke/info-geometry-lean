#!/usr/bin/env python3
"""Resolve Leanstral model aliases from startup config files."""
from __future__ import annotations

import argparse
import json
import shlex
import re
import sys
from dataclasses import dataclass
from pathlib import Path
from typing import Any

if __package__ in (None, ""):
    REPO_ROOT = Path(__file__).resolve().parents[2]
    if str(REPO_ROOT) not in sys.path:
        sys.path.insert(0, str(REPO_ROOT))

from tools.infra.leanstral_model_utils import choose_matching_model, fetch_model_ids

try:
    import yaml  # type: ignore
except Exception:  # pragma: no cover - fallback only
    yaml = None


_ASSISTANTS_KEY = "assistants"
_LANES_KEY = "lanes"
_MODEL_KEY = "model"


def _strip_comments(line: str) -> str:
    value = line.split("#", 1)[0]
    return value.rstrip()


@dataclass(frozen=True)
class LaneResult:
    namespace: str
    lane: str
    configured: str
    resolved: str
    resolved_ok: bool


def _parse_yaml(path: Path) -> dict[str, Any]:
    if not path.exists():
        return {}
    if yaml is None:
        return _parse_yaml_fallback(path)
    payload = yaml.safe_load(path.read_text(encoding="utf-8"))
    return payload if isinstance(payload, dict) else {}


def _parse_yaml_fallback(path: Path) -> dict[str, Any]:
    """Minimal parser fallback for simple startup config shape."""
    out: dict[str, Any] = {}
    current_section = ""
    current_item: str | None = None

    for raw_line in path.read_text(encoding="utf-8").splitlines():
        line = _strip_comments(raw_line)
        if not line.strip():
            continue
        leading = len(raw_line) - len(raw_line.lstrip(" "))
        if leading % 2 != 0:
            continue

        if leading == 0:
            current_section = ""
            current_item = None
            if m := re.match(r"^([A-Za-z0-9_-]+)\s*:\s*(.*)\s*$", line):
                key = m.group(1)
                value = m.group(2).strip()
                if value:
                    out.setdefault(key, value)
                elif key in (_ASSISTANTS_KEY, _LANES_KEY):
                    current_section = key
                    out.setdefault(key, {})
            continue

        if current_section not in {_ASSISTANTS_KEY, _LANES_KEY}:
            continue

        if leading == 2:
            if m := re.match(r"^\s{2}([A-Za-z0-9_-]+)\s*:\s*(.*)\s*$", line):
                name = m.group(1)
                value = m.group(2).strip()
                if value:
                    out[current_section][name] = value
                    current_item = None
                else:
                    current_item = name
                    out[current_section].setdefault(name, {})
                continue

        if current_item is not None and leading == 4:
            if m := re.match(r"^\s{4}([A-Za-z0-9_-]+)\s*:\s*(.*)\s*$", line):
                item_key = m.group(1).strip()
                if item_key != _MODEL_KEY:
                    continue
                value = m.group(2).strip()
                out[current_section][current_item][_MODEL_KEY] = value
            continue

    return out


def _value_from_path(payload: dict[str, Any], segments: list[str]) -> str:
    node: Any = payload
    for segment in segments:
        if not isinstance(node, dict):
            return ""
        value = node.get(segment, "")
        if isinstance(value, dict) or isinstance(value, str):
            node = value
        else:
            return ""
    return str(node).strip() if isinstance(node, str) else ""


def _env_prefix(namespace: str, lane: str) -> str:
    return re.sub(r"[^A-Za-z0-9_]", "_", f"{namespace}_{lane}".upper())


def _legacy_key(namespace: str, lane: str) -> str | None:
    if namespace == "archon" and lane == "leanstral":
        return "ARCHON_LEANSTRAL_MODEL"
    if namespace == "nemoclaw" and lane == "planner_engine":
        return "NEMOCLAW_PLANNER_ENGINE_MODEL"
    if namespace == "nemoclaw" and lane == "logic_engine":
        return "NEMOCLAW_LOGIC_ENGINE_MODEL"
    if namespace == "nemoclaw" and lane == "discovery_engine":
        return "NEMOCLAW_DISCOVERY_ENGINE_MODEL"
    return None


def collect_requested_models(archon_config: Path, nemoclaw_config: Path) -> list[tuple[str, str, str]]:
    requested: list[tuple[str, str, str]] = []
    archon_payload = _parse_yaml(archon_config)
    assistants = archon_payload.get(_ASSISTANTS_KEY, {})
    if isinstance(assistants, dict):
        for name, cfg in assistants.items():
            model = ""
            if isinstance(cfg, dict):
                value = cfg.get("model", "")
                model = str(value).strip() if isinstance(value, str) else ""
            if not model or not isinstance(name, str):
                continue
            requested.append(("archon", str(name).strip(), model))

    nemoclaw_payload = _parse_yaml(nemoclaw_config)
    lanes = nemoclaw_payload.get("lanes", {})
    if isinstance(lanes, dict):
        for lane, cfg in lanes.items():
            model = ""
            if isinstance(cfg, dict):
                value = cfg.get("model", "")
                model = str(value).strip() if isinstance(value, str) else ""
            if not model or not isinstance(lane, str):
                continue
            requested.append(("nemoclaw", str(lane).strip(), model))
    return requested


def resolve_requested_models(
    base_url: str,
    requests: list[tuple[str, str, str]],
    timeout: int,
    *,
    defaults_only: bool = False,
) -> list[LaneResult]:
    if defaults_only:
        return [LaneResult(namespace, lane, model, model, False) for namespace, lane, model in requests]

    status, ids, _ = fetch_model_ids(base_url, timeout)
    resolved: list[LaneResult] = []
    if 200 <= status < 300 and ids:
        for namespace, lane, model in requests:
            matched = choose_matching_model(model, ids, fallback_to_first=False)
            if matched:
                resolved.append(LaneResult(namespace, lane, model, matched, True))
            else:
                resolved.append(LaneResult(namespace, lane, model, model, False))
        return resolved

    return [LaneResult(namespace, lane, model, model, False) for namespace, lane, model in requests]


def to_payload(results: list[LaneResult]) -> dict[str, Any]:
    configured: dict[str, dict[str, str]] = {}
    resolved: dict[str, dict[str, str]] = {}
    resolved_count = 0
    for item in results:
        configured.setdefault(item.namespace, {})[item.lane] = item.configured
        resolved.setdefault(item.namespace, {})[item.lane] = item.resolved
        if item.resolved_ok:
            resolved_count += 1

    query_ok = len(results) > 0
    return {
        "configured": configured,
        "resolved": resolved,
        "status": {
            "query_ok": query_ok,
            "resolved_count": resolved_count,
            "resolved_ok": query_ok and resolved_count == len(results),
        },
    }


def to_env_lines(results: list[LaneResult]) -> str:
    values: dict[str, str] = {
        "ARCHON_LEANSTRAL_MODEL": "",
        "NEMOCLAW_PLANNER_ENGINE_MODEL": "",
        "NEMOCLAW_LOGIC_ENGINE_MODEL": "",
        "NEMOCLAW_DISCOVERY_ENGINE_MODEL": "",
    }
    for item in results:
        legacy = _legacy_key(item.namespace, item.lane)
        if legacy is not None:
            values[legacy] = item.resolved
        values[f"{_env_prefix(item.namespace, item.lane)}_MODEL"] = item.resolved
    return "\n".join(f"{name}={shlex.quote(value)}" for name, value in values.items())


def _parse_args() -> argparse.Namespace:
    parser = argparse.ArgumentParser(description="Resolve Leanstral config aliases against local endpoint models.")
    parser.add_argument("--base-url", default="http://127.0.0.1:18889/v1")
    parser.add_argument("--archon-config", type=Path, default=Path(".archon/config.yaml"))
    parser.add_argument("--nemoclaw-config", type=Path, default=Path("nemoclaw_config.yaml"))
    parser.add_argument("--timeout", type=float, default=3.0)
    parser.add_argument("--format", choices=("json", "env"), default="json")
    parser.add_argument("--defaults-only", action="store_true", help="Skip endpoint probing and return configured model IDs.")
    parser.add_argument("--json-out", type=Path, default=None, help="Optional destination for JSON payload.")
    return parser.parse_args()


def main() -> int:
    args = _parse_args()
    requests = collect_requested_models(args.archon_config, args.nemoclaw_config)
    if requests:
        results = resolve_requested_models(
            args.base_url, requests, int(args.timeout), defaults_only=args.defaults_only
        )
    else:
        results = []

    payload = to_payload(results)
    if args.format == "env":
        text = to_env_lines(results) + "\n"
        if args.json_out:
            args.json_out.parent.mkdir(parents=True, exist_ok=True)
            args.json_out.write_text(json.dumps(payload, indent=2, sort_keys=True, ensure_ascii=True) + "\n", encoding="utf-8")
        else:
            print(text, end="")
        return 0

    text = json.dumps(payload, indent=2, sort_keys=True, ensure_ascii=True) + "\n"
    if args.json_out:
        args.json_out.parent.mkdir(parents=True, exist_ok=True)
        args.json_out.write_text(text, encoding="utf-8")
    else:
        print(text, end="")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
