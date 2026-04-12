#!/usr/bin/env python3
from __future__ import annotations

import argparse
import sys
from pathlib import Path
from typing import Any

import yaml

ROOT = Path(__file__).resolve().parents[2]

SOUL_POLICY = ROOT / "tools/prompts/SOUL_POLICY.md"
HEARTBEAT_POLICY = ROOT / "tools/prompts/HEARTBEAT_POLICY.md"
PUBLISH_POLICY = ROOT / "tools/prompts/PUBLISH_GATE_POLICY.md"
SYMBOL_FIRST_POLICY = ROOT / "tools/prompts/SYMBOL_FIRST_PROTOCOL.md"
DEFAULT_CONFIG = ROOT / "nemoclaw_config.yaml"

REQUIRED_TEXT: dict[Path, tuple[str, ...]] = {
    SOUL_POLICY: (
        "No reputational actions against individuals.",
        "Never optimize by social pressure or coercion.",
        "When blocked by policy, de-escalate and request human decision.",
    ),
    HEARTBEAT_POLICY: (
        "Heartbeat may run only in `prove` or `orchestrate` planes.",
        "Heartbeat is forbidden in `publish` plane.",
        "All outbound writes require publish gate approval.",
    ),
    PUBLISH_POLICY: (
        "Two-key approval is mandatory for any outbound internet write.",
        "Key 1: human.",
        "Key 2: policy_engine.",
        "Default policy is deny for publish.",
    ),
    SYMBOL_FIRST_POLICY: (
        "Exploration is **symbol-first**.",
        "Natural language is a coordination layer, not the primary search surface.",
        "Only compiled Lean terms are authoritative.",
    ),
}

REQUIRED_LINKAGE_TEXT: dict[Path, tuple[str, ...]] = {
    ROOT / "tools/prompts/jungian_pass.md": (
        "SYMBOL_FIRST_PROTOCOL.md",
        "No language-only output.",
    ),
    ROOT / "tools/prompts/pauli_pass.md": (
        "SYMBOL_FIRST_PROTOCOL.md",
        "Reject language-only packets.",
    ),
    ROOT / "tools/frontier/generative_loop_spec.md": (
        "symbol-first",
        "Natural language is coordination-only.",
    ),
    ROOT / "tools/prompts/agentic_autotheory_prompts_2026-04-15.md": (
        "Symbol-first exploration is mandatory; language is coordination-only.",
        "SYMBOL_FIRST_PROTOCOL.md",
    ),
    ROOT / "tools/prompts/agentic_handover_policy_2026-04-15.md": (
        "Exploration in this stack is symbol-first; language is coordination-only.",
        "SYMBOL_FIRST_PROTOCOL.md",
    ),
}


def _as_dict(obj: Any) -> dict[str, Any]:
    return obj if isinstance(obj, dict) else {}


def _as_list(obj: Any) -> list[Any]:
    return obj if isinstance(obj, list) else []


def _must_contain(path: Path, snippets: tuple[str, ...], errors: list[str]) -> None:
    if not path.exists():
        errors.append(f"missing policy file: {path.relative_to(ROOT)}")
        return
    text = path.read_text(encoding="utf-8")
    for snippet in snippets:
        if snippet not in text:
            errors.append(f"{path.relative_to(ROOT)} missing required text: {snippet!r}")


def _load_yaml(path: Path, errors: list[str]) -> dict[str, Any]:
    if not path.exists():
        errors.append(f"missing config file: {path.relative_to(ROOT)}")
        return {}
    try:
        raw = yaml.safe_load(path.read_text(encoding="utf-8"))
    except Exception as exc:  # pragma: no cover - safety path
        errors.append(f"failed to parse {path.relative_to(ROOT)}: {type(exc).__name__}: {exc}")
        return {}
    return _as_dict(raw)


def _check_linkage(errors: list[str]) -> None:
    for path, snippets in REQUIRED_LINKAGE_TEXT.items():
        _must_contain(path, snippets, errors)


def _check_runtime_policy(config: dict[str, Any], errors: list[str]) -> None:
    runtime = _as_dict(config.get("runtime_policy"))
    if not runtime:
        errors.append("nemoclaw_config.yaml missing runtime_policy section")
        return

    planes = _as_dict(runtime.get("planes"))
    allowed_planes = set(_as_list(planes.get("allowed")))
    default_plane = planes.get("default")

    required_planes = {"prove", "orchestrate", "publish"}
    if not required_planes.issubset(allowed_planes):
        errors.append(
            "runtime_policy.planes.allowed must include prove/orchestrate/publish"
        )
    if default_plane == "publish":
        errors.append("runtime_policy.planes.default must not be publish")
    if default_plane not in {"prove", "orchestrate"}:
        errors.append("runtime_policy.planes.default must be prove or orchestrate")

    heartbeat = _as_dict(runtime.get("heartbeat"))
    hb_allowed = set(_as_list(heartbeat.get("allowed_planes")))
    if not heartbeat.get("enabled", False):
        errors.append("runtime_policy.heartbeat.enabled must be true")
    if "publish" in hb_allowed:
        errors.append("runtime_policy.heartbeat.allowed_planes must not include publish")
    if not hb_allowed.issubset({"prove", "orchestrate"}):
        errors.append(
            "runtime_policy.heartbeat.allowed_planes must be subset of {prove, orchestrate}"
        )

    publish = _as_dict(runtime.get("publish"))
    publish_enabled = bool(publish.get("enabled", False))
    if publish.get("default_policy") != "deny":
        errors.append("runtime_policy.publish.default_policy must be deny")
    if publish.get("require_two_key_approval") is not True:
        errors.append("runtime_policy.publish.require_two_key_approval must be true")
    approval_keys = set(_as_list(publish.get("approval_keys")))
    if not {"human", "policy_engine"}.issubset(approval_keys):
        errors.append(
            "runtime_policy.publish.approval_keys must include human and policy_engine"
        )

    tools = _as_list(config.get("tools"))
    publish_tools = [
        _as_dict(t)
        for t in tools
        if _as_dict(t).get("allows_outbound_publish") is True and _as_dict(t).get("enabled") is True
    ]
    for tool in publish_tools:
        if tool.get("allowed_plane") != "publish":
            errors.append(
                f"publish-capable tool {tool.get('name', '<unknown>')} must set allowed_plane=publish"
            )

    if publish_tools:
        if not publish_enabled:
            errors.append(
                "publish-capable tool is enabled while runtime_policy.publish.enabled is false"
            )
        if publish.get("require_two_key_approval") is not True or not {
            "human",
            "policy_engine",
        }.issubset(approval_keys):
            errors.append(
                "publish-capable run configured without mandatory two-key approval"
            )


def main() -> int:
    parser = argparse.ArgumentParser(
        description="Enforce agentic autonomy policy (SOUL/HEARTBEAT/PUBLISH + runtime config)."
    )
    parser.add_argument(
        "--config",
        type=Path,
        default=DEFAULT_CONFIG,
        help="Path to runtime config yaml (default: nemoclaw_config.yaml)",
    )
    args = parser.parse_args()

    errors: list[str] = []
    for policy_path, snippets in REQUIRED_TEXT.items():
        _must_contain(policy_path, snippets, errors)
    _check_linkage(errors)

    config = _load_yaml(args.config, errors)
    if config:
        _check_runtime_policy(config, errors)

    if errors:
        print("[agentic-policy] failures detected:")
        for err in errors:
            print(f"  - {err}")
        return 1

    print("[agentic-policy] policy OK")
    return 0


if __name__ == "__main__":
    sys.exit(main())
