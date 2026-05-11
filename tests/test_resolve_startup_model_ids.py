from __future__ import annotations

from pathlib import Path
from typing import Any

from tools.infra import resolve_startup_model_ids


def test_collect_requested_models_includes_leanstral_and_nemoclaw_lanes(tmp_path: Path) -> None:
    archon_cfg = tmp_path / "config.yaml"
    nemoclaw_cfg = tmp_path / "nemoclaw_config.yaml"

    archon_cfg.write_text(
        """
assistant: pi
assistants:
  leanstral:
    model: local/leanstral-alias
  pi:
    model: openrouter/owl-alpha
"""
        .strip()
        + "\n",
        encoding="utf-8",
    )
    nemoclaw_cfg.write_text(
        """
version: "1.1"
lanes:
  planner_engine:
    model: /models/plan.gguf
    base_url: http://127.0.0.1:18889/v1
  logic_engine:
    model: /models/logic.gguf
    base_url: http://127.0.0.1:18889/v1
  discovery_engine:
    model: qwen/qwen-2.5
    base_url: http://127.0.0.1:8001/v1
"""
        .strip()
        + "\n",
        encoding="utf-8",
    )

    requests = resolve_startup_model_ids.collect_requested_models(archon_cfg, nemoclaw_cfg)
    assert ("archon", "leanstral", "local/leanstral-alias") in requests
    assert ("archon", "pi", "openrouter/owl-alpha") in requests
    assert ("nemoclaw", "planner_engine", "/models/plan.gguf") in requests
    assert ("nemoclaw", "logic_engine", "/models/logic.gguf") in requests
    assert ("nemoclaw", "discovery_engine", "qwen/qwen-2.5") in requests


def test_collect_requested_models_without_pyyaml_falls_back_to_simple_parser(tmp_path: Path, monkeypatch: Any) -> None:
    monkeypatch.setattr(resolve_startup_model_ids, "yaml", None)
    archon_cfg = tmp_path / "config.yaml"
    nemoclaw_cfg = tmp_path / "nemoclaw_config.yaml"
    archon_cfg.write_text(
        """
assistant: pi
assistants:
  leanstral:
    model: local/leanstral
  pi:
    model: openrouter/owl-alpha
"""
        .strip()
        + "\n",
        encoding="utf-8",
    )
    nemoclaw_cfg.write_text(
        """
version: "1.1"
lanes:
  planner_engine:
    model: /models/plan.gguf
  logic_engine:
    model: /models/logic.gguf
  discovery_engine:
    model: qwen/qwen-2.5
"""
        .strip()
        + "\n",
        encoding="utf-8",
    )

    requests = resolve_startup_model_ids.collect_requested_models(archon_cfg, nemoclaw_cfg)
    assert ("archon", "leanstral", "local/leanstral") in requests
    assert ("archon", "pi", "openrouter/owl-alpha") in requests
    assert ("nemoclaw", "planner_engine", "/models/plan.gguf") in requests
    assert ("nemoclaw", "logic_engine", "/models/logic.gguf") in requests
    assert ("nemoclaw", "discovery_engine", "qwen/qwen-2.5") in requests


def test_defaults_only_does_not_query_endpoints(monkeypatch: Any) -> None:
    requests = [
        ("archon", "leanstral", "local/leanstral-alias"),
        ("nemoclaw", "planner_engine", "/models/plan.gguf"),
    ]

    monkeypatch.setattr(resolve_startup_model_ids, "fetch_model_ids", lambda *_args, **_kwargs: (_ for _ in ()).throw(AssertionError("endpoint should not be called")))
    results = resolve_startup_model_ids.resolve_requested_models("http://127.0.0.1:18889/v1", requests, timeout=3, defaults_only=True)

    assert results == [
        resolve_startup_model_ids.LaneResult("archon", "leanstral", "local/leanstral-alias", "local/leanstral-alias", False),
        resolve_startup_model_ids.LaneResult("nemoclaw", "planner_engine", "/models/plan.gguf", "/models/plan.gguf", False),
    ]


def test_to_env_lines_includes_generic_lane_aliases() -> None:
    results = [
        resolve_startup_model_ids.LaneResult(
            "archon",
            "leanstral",
            "local/leanstral-alias",
            "leanstral-gguf",
            True,
        ),
        resolve_startup_model_ids.LaneResult(
            "nemoclaw",
            "planner_engine",
            "/models/plan.gguf",
            "/models/plan_resolved.gguf",
            True,
        ),
        resolve_startup_model_ids.LaneResult(
            "nemoclaw",
            "discovery_engine",
            "qwen/qwen-2.5",
            "/models/discover_resolved.q4_k_m.gguf",
            True,
        ),
        resolve_startup_model_ids.LaneResult(
            "nemoclaw",
            "new_lane",
            "qwen/phi",
            "phi",
            True,
        ),
    ]
    text = resolve_startup_model_ids.to_env_lines(results)
    lines = text.strip().splitlines()
    env = {ln.split("=", 1)[0]: ln.split("=", 1)[1].strip() for ln in lines}

    def unquote(value: str) -> str:
        return value[1:-1] if (value.startswith("'") and value.endswith("'")) else value

    assert unquote(env["ARCHON_LEANSTRAL_MODEL"]) == "leanstral-gguf"
    assert unquote(env["NEMOCLAW_PLANNER_ENGINE_MODEL"]) == "/models/plan_resolved.gguf"
    assert unquote(env["NEMOCLAW_DISCOVERY_ENGINE_MODEL"]) == "/models/discover_resolved.q4_k_m.gguf"
    assert unquote(env["NEMOCLAW_NEW_LANE_MODEL"]) == "phi"
