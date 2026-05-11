#!/usr/bin/env python3
"""Check the resident local model endpoint and config alignment.

This is an operational health probe only. It does not certify proof authority,
model quality, or Hive promotion eligibility.
"""

from __future__ import annotations

import argparse
import json
import urllib.error
import urllib.request
from pathlib import Path
from typing import Any

from tools.infra.leanstral_model_utils import choose_matching_model, parse_model_ids, resolve_with_expected


SCHEMA = "info_geometry.resident_model_endpoint_check.v1"


def http_json(url: str, *, timeout: float, payload: dict[str, Any] | None = None) -> tuple[int, Any, str]:
    data = None
    headers = {"Accept": "application/json"}
    method = "GET"
    if payload is not None:
        data = json.dumps(payload, ensure_ascii=True).encode("utf-8")
        headers["Content-Type"] = "application/json"
        method = "POST"
    req = urllib.request.Request(url, data=data, headers=headers, method=method)
    try:
        with urllib.request.urlopen(req, timeout=timeout) as resp:  # noqa: S310 local operator endpoint
            text = resp.read().decode("utf-8", errors="replace")
            try:
                parsed = json.loads(text)
            except Exception:
                parsed = None
            return int(resp.status), parsed, text
    except urllib.error.HTTPError as exc:
        text = exc.read().decode("utf-8", errors="replace")
        try:
            parsed = json.loads(text)
        except Exception:
            parsed = None
        return int(exc.code), parsed, text
    except Exception as exc:  # noqa: BLE001
        return 0, None, repr(exc)


def yaml_scalar_after(lines: list[str], key: str, *, start: int = 0, end: int | None = None) -> str:
    end = len(lines) if end is None else end
    prefix = f"{key}:"
    for line in lines[start:end]:
        stripped = line.strip()
        if stripped.startswith(prefix):
            value = stripped[len(prefix) :].strip()
            if (value.startswith('"') and value.endswith('"')) or (value.startswith("'") and value.endswith("'")):
                value = value[1:-1]
            return value
    return ""


def block_bounds(lines: list[str], marker: str) -> tuple[int, int] | None:
    start = None
    marker_prefix = f"{marker}:"
    for idx, line in enumerate(lines):
        if line.strip().startswith(marker_prefix):
            start = idx + 1
            break
    if start is None:
        return None
    end = len(lines)
    for idx in range(start, len(lines)):
        line = lines[idx]
        if line and not line.startswith(" ") and line.strip().endswith(":"):
            end = idx
            break
    return start, end


def hermes_default(path: Path) -> str:
    if not path.exists():
        return ""
    return yaml_scalar_after(path.read_text(encoding="utf-8").splitlines(), "default")


def nemoclaw_lane_model(path: Path, lane: str) -> str:
    if not path.exists():
        return ""
    lines = path.read_text(encoding="utf-8").splitlines()
    bounds = block_bounds(lines, lane)
    if bounds is None:
        return ""
    return yaml_scalar_after(lines, "model", start=bounds[0], end=bounds[1])


def chat_probe_payload(model: str) -> dict[str, Any]:
    return {
        "model": model,
        "messages": [
            {"role": "system", "content": "You are a concise health-check endpoint."},
            {"role": "user", "content": "Reply with exactly: ok"},
        ],
        "temperature": 0,
        "max_tokens": 8,
    }


def choose_expected_model(expected_model: str, ids: list[str]) -> str:
    if not expected_model or not ids:
        return expected_model
    resolved = choose_matching_model(expected_model, ids, fallback_to_first=False, require_match=True)
    return resolved


def run_check(
    *,
    base_url: str,
    expected_model: str,
    timeout: float,
    hermes_config: Path | None = None,
    nemoclaw_config: Path | None = None,
    probe_chat: bool = False,
) -> dict[str, Any]:
    base = base_url.rstrip("/")
    models_status, models_payload, models_raw = http_json(f"{base}/models", timeout=timeout)
    ids = parse_model_ids(models_payload)
    resolved_expected = choose_expected_model(expected_model, ids)
    model_present = bool(expected_model and ids and resolved_expected)

    chat = {
        "enabled": probe_chat,
        "status": None,
        "ok": None,
        "error": None,
    }
    if probe_chat:
        if not expected_model:
            chat.update({"ok": False, "error": "--expected-model is required for --probe-chat"})
        else:
            status, payload, raw = http_json(
                f"{base}/chat/completions",
                timeout=timeout,
                payload=chat_probe_payload(resolved_expected or expected_model),
            )
            chat.update(
                {
                    "status": status,
                    "ok": 200 <= status < 300 and isinstance(payload, dict),
                    "error": None if 200 <= status < 300 else raw[:1000],
                }
            )

    hermes_model = hermes_default(hermes_config) if hermes_config else ""
    planner_model = nemoclaw_lane_model(nemoclaw_config, "planner_engine") if nemoclaw_config else ""
    logic_model = nemoclaw_lane_model(nemoclaw_config, "logic_engine") if nemoclaw_config else ""
    config_matches = {
        "hermes_default_matches": not hermes_config or resolve_with_expected(expected_model, hermes_model, ids) != "",
        "nemoclaw_planner_matches": not nemoclaw_config
        or resolve_with_expected(expected_model, planner_model, ids) != "",
        "nemoclaw_logic_matches": not nemoclaw_config or resolve_with_expected(expected_model, logic_model, ids) != "",
    }

    ok = (
        200 <= models_status < 300
        and model_present
        and all(config_matches.values())
        and (not probe_chat or bool(chat["ok"]))
    )
    return {
        "schema": SCHEMA,
        "ok": ok,
        "base_url": base,
        "expected_model": expected_model,
        "models": {
            "status": models_status,
            "ids": ids,
            "expected_present": model_present,
            "expected_model_resolved": resolved_expected,
            "resolved_candidates": {
                "hermes_default": resolve_with_expected(expected_model, hermes_model, ids),
                "nemoclaw_planner_model": resolve_with_expected(expected_model, planner_model, ids),
                "nemoclaw_logic_model": resolve_with_expected(expected_model, logic_model, ids),
            },
            "raw_excerpt": models_raw[:1000] if models_status == 0 or not isinstance(models_payload, dict) else "",
        },
        "chat_probe": chat,
        "config": {
            "hermes_config": str(hermes_config) if hermes_config else None,
            "hermes_default": hermes_model,
            "nemoclaw_config": str(nemoclaw_config) if nemoclaw_config else None,
            "nemoclaw_planner_model": planner_model,
            "nemoclaw_logic_model": logic_model,
            **config_matches,
        },
        "authority_boundary": {
            "health_check_only": True,
            "not_a_proof_certificate": True,
            "lean_remains_proof_authority": True,
        },
    }


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--base-url", default="http://127.0.0.1:18889/v1")
    parser.add_argument("--expected-model", default="leanstral-gguf")
    parser.add_argument("--timeout", type=float, default=10)
    parser.add_argument("--hermes-config", type=Path, default=Path("tools/infra/hermes_config.yaml"))
    parser.add_argument("--nemoclaw-config", type=Path, default=Path("nemoclaw_config.yaml"))
    parser.add_argument("--probe-chat", action="store_true")
    parser.add_argument("--json-out", type=Path)
    args = parser.parse_args()

    report = run_check(
        base_url=args.base_url,
        expected_model=args.expected_model,
        timeout=args.timeout,
        hermes_config=args.hermes_config,
        nemoclaw_config=args.nemoclaw_config,
        probe_chat=bool(args.probe_chat),
    )
    text = json.dumps(report, indent=2, ensure_ascii=True, sort_keys=True) + "\n"
    if args.json_out:
        args.json_out.parent.mkdir(parents=True, exist_ok=True)
        args.json_out.write_text(text, encoding="utf-8")
    print(text, end="")
    return 0 if report["ok"] else 2


if __name__ == "__main__":
    raise SystemExit(main())
