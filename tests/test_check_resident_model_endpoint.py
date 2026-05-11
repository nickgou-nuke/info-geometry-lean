from __future__ import annotations

from pathlib import Path

from tools.infra import check_resident_model_endpoint as check


def test_run_check_passes_against_mock_endpoint(tmp_path: Path, monkeypatch) -> None:
    calls: list[tuple[str, dict | None]] = []

    def fake_http_json(url: str, timeout: float, payload=None) -> tuple[int, dict, str]:
        calls.append((url, payload))
        if url.endswith("/models"):
            return 200, {"data": [{"id": "leanstral-gguf"}]}, ""
        if url.endswith("/chat/completions"):
            assert payload is not None
            return 200, {"choices": [{"message": {"content": "ok"}}]}, ""
        return 404, {"error": "unknown"}, ""

    monkeypatch.setattr(check, "http_json", fake_http_json)

    hermes = tmp_path / "hermes.yaml"
    nemoclaw = tmp_path / "nemoclaw.yaml"
    hermes.write_text("model:\n  default: leanstral-gguf\n", encoding="utf-8")
    nemoclaw.write_text(
        "lanes:\n"
        "  planner_engine:\n"
        "    model: \"leanstral-gguf\"\n"
        "  logic_engine:\n"
        "    model: \"leanstral-gguf\"\n",
        encoding="utf-8",
    )

    report = check.run_check(
        base_url="http://127.0.0.1:18889/v1",
        expected_model="leanstral-gguf",
        timeout=3,
        hermes_config=hermes,
        nemoclaw_config=nemoclaw,
        probe_chat=True,
    )

    assert report["ok"] is True
    assert report["models"]["expected_present"] is True
    assert report["chat_probe"]["ok"] is True
    assert report["config"]["hermes_default_matches"] is True
    assert any(url.endswith("/chat/completions") for url, _ in calls)


def test_run_check_detects_config_mismatch(tmp_path: Path, monkeypatch) -> None:
    def fake_http_json(url: str, timeout: float, payload=None) -> tuple[int, dict, str]:
        if url.endswith("/models"):
            return 200, {"data": [{"id": "leanstral-gguf"}]}, ""
        if url.endswith("/chat/completions"):
            return 200, {"choices": [{"message": {"content": "ok"}}]}, ""
        return 404, {"error": "unknown"}, ""

    monkeypatch.setattr(check, "http_json", fake_http_json)

    hermes = tmp_path / "hermes.yaml"
    hermes.write_text("model:\n  default: other-model\n", encoding="utf-8")

    report = check.run_check(
        base_url="http://127.0.0.1:18889/v1",
        expected_model="leanstral-gguf",
        timeout=3,
        hermes_config=hermes,
        nemoclaw_config=None,
        probe_chat=False,
    )

    assert report["ok"] is False
    assert report["config"]["hermes_default_matches"] is False


def test_run_check_tolerates_endpoint_alias_for_expected_model(tmp_path: Path, monkeypatch) -> None:
    capture: list[dict] = []

    def fake_http_json(url: str, timeout: float, payload=None) -> tuple[int, dict, str]:
        if url.endswith("/models"):
            return 200, {"data": [{"id": "/models/mistralai_Leanstral-128x3.9B-2603-Q4_K_M.gguf"}]}, ""
        if url.endswith("/chat/completions"):
            capture.append(payload or {})
            assert payload is not None
            return 200, {"choices": [{"message": {"content": "ok"}}]}, ""
        return 404, {"error": "unknown"}, ""

    monkeypatch.setattr(check, "http_json", fake_http_json)

    hermes = tmp_path / "hermes.yaml"
    hermes.write_text("model:\n  default: leanstral-gguf\n", encoding="utf-8")

    report = check.run_check(
        base_url="http://127.0.0.1:18889/v1",
        expected_model="leanstral-gguf",
        timeout=3,
        hermes_config=hermes,
        nemoclaw_config=None,
        probe_chat=True,
    )

    assert report["ok"] is True
    assert report["models"]["expected_present"] is True
    assert report["models"]["expected_model_resolved"] == "/models/mistralai_Leanstral-128x3.9B-2603-Q4_K_M.gguf"
    assert report["chat_probe"]["ok"] is True
    assert capture
    assert capture[0]["model"] == "/models/mistralai_Leanstral-128x3.9B-2603-Q4_K_M.gguf"
    assert report["config"]["hermes_default_matches"] is True
