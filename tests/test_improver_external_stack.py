from __future__ import annotations

import os
import sys
from pathlib import Path


REPO = Path(__file__).resolve().parents[1]
IMPROVER = REPO / "external_refs" / "ImProver"


def test_improver_external_stack_imports_offline_metrics(monkeypatch) -> None:
    monkeypatch.delenv("OPENAI_API_KEY", raising=False)
    sys.path.insert(0, str(IMPROVER))
    try:
        from evaluate.metrics import length_metric
        from models.structures import Theorem

        metric = length_metric()
    finally:
        try:
            sys.path.remove(str(IMPROVER))
        except ValueError:
            pass

    assert Theorem.__name__ == "Theorem"
    assert metric.name == "LENGTH"
    assert metric.vs is None
    assert os.getenv("OPENAI_API_KEY") is None


def test_improver_prompt_routes_leanstral_to_local_openai_endpoint(monkeypatch) -> None:
    sys.path.insert(0, str(IMPROVER))
    calls: list[dict] = []

    class FakeChatOpenAI:
        def __init__(self, **kwargs):
            calls.append(kwargs)

    try:
        import models.prompt as prompt

        monkeypatch.setattr(prompt, "ChatOpenAI", FakeChatOpenAI)
        monkeypatch.delenv("IMPROVER_LLM_BASE_URL", raising=False)
        monkeypatch.delenv("OPENCLAW_LLM_BASE_URL", raising=False)
        monkeypatch.delenv("LEANSTRAL_BASE_URL", raising=False)
        prompt.make_chat_model("leanstral-gguf")

        monkeypatch.setenv("IMPROVER_LLM_BASE_URL", "http://127.0.0.1:30002/v1")
        monkeypatch.setenv("IMPROVER_LLM_API_KEY", "local-token")
        prompt.make_chat_model("custom-local")
    finally:
        try:
            sys.path.remove(str(IMPROVER))
        except ValueError:
            pass

    assert calls[0] == {
        "model": "leanstral-gguf",
        "base_url": "http://127.0.0.1:18889/v1",
        "api_key": "token-123",
    }
    assert calls[1] == {
        "model": "custom-local",
        "base_url": "http://127.0.0.1:30002/v1",
        "api_key": "local-token",
    }
