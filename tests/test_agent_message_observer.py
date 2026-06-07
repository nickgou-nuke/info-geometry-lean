import json
import subprocess
import sys
from pathlib import Path
from types import SimpleNamespace

from tools.infra import agent_message_ledger as ledger
from tools.infra import gepa_agent_message_observer as observer


def test_redaction_clipping_and_hash_preserve_original_identity() -> None:
    secret = "sk-" + "a" * 32
    text = f"token={secret}\n" + ("x" * 80)

    redacted, hits = ledger.redact_text(text)
    assert secret not in redacted
    assert "openai_key" in hits

    clipped, truncated = ledger.clip_text(redacted, max_chars=40)
    assert truncated is True
    assert "[... clipped" in clipped
    assert ledger.sha256_text(text) != ledger.sha256_text(redacted)


def test_record_message_writes_redacted_jsonl(tmp_path: Path) -> None:
    secret = "Bearer " + "b" * 40
    event = ledger.record_message(
        source_tool="unit",
        source_file="tests/test_agent_message_observer.py",
        channel="unit_channel",
        provider="provider",
        model="model",
        prompt_text=f"send {secret}",
        response_text="ok",
        success=True,
        latency_ms=12.5,
        correlation_id="corr",
        metadata={"path": tmp_path, "nested": {"n": 1}},
        ledger_dir=tmp_path,
        max_text_chars=200,
    )

    files = list(tmp_path.glob("*_agent_messages.jsonl"))
    assert len(files) == 1
    row = json.loads(files[0].read_text(encoding="utf-8"))
    assert row["event_id"] == event["event_id"]
    assert row["prompt_sha256"] == ledger.sha256_text(f"send {secret}")
    assert secret not in row["prompt_text"]
    assert "bearer_token" in row["prompt_sensitive_matches"]
    assert row["metadata"]["path"] == str(tmp_path)
    assert row["authority"] == "observation_only_not_proof"


def test_observe_ledger_file_classifies_failures(tmp_path: Path) -> None:
    ledger.record_message(
        source_tool="unit",
        source_file="tests/test_agent_message_observer.py",
        channel="oracle",
        provider="chatgpt",
        model="browser",
        prompt_text="prove theorem",
        response_text="ORACLE ERROR: browser lane failed",
        success=False,
        metadata={},
        ledger_dir=tmp_path,
    )

    path = next(tmp_path.glob("*_agent_messages.jsonl"))
    observations = observer.observe_ledger_file(path)
    assert len(observations) == 1
    obs = observations[0]
    assert obs.source_kind == "agent_message_ledger"
    assert obs.provider == "chatgpt"
    assert obs.success is False
    assert obs.failure_pattern == "oracle_error"
    assert obs.outcome()["status"] == "failed"


def test_collect_legacy_artifact_and_recommendations(tmp_path: Path) -> None:
    legacy = tmp_path / "legacy"
    legacy.mkdir()
    prompt = legacy / "gemini_prompt.txt"
    prompt.write_text("x" * 25000, encoding="utf-8")

    args = SimpleNamespace(
        ledger=False,
        ledger_dir=str(tmp_path / "none"),
        gepa_cache=False,
        legacy_artifacts=True,
        legacy_root=[str(legacy)],
        legacy_limit=10,
        limit=10,
    )
    observations = observer.collect(args)
    assert len(observations) == 1
    assert observations[0].provider == "gemini"
    assert observations[0].failure_pattern == "unscored_legacy_prompt"

    recs = observer.recommendations(observations)
    assert any("Summarize retrieved context" in rec["candidate"] for rec in recs)


def test_observer_cli_writes_report_and_review_packet(tmp_path: Path) -> None:
    ledger_dir = tmp_path / "ledger"
    out_dir = tmp_path / "out"
    review_dir = tmp_path / "review"

    ledger.record_message(
        source_tool="unit",
        source_file="tests/test_agent_message_observer.py",
        channel="cli_channel",
        provider="pi",
        model="deepseek",
        prompt_text="prompt",
        response_text="response",
        success=True,
        latency_ms=3.0,
        ledger_dir=ledger_dir,
    )

    proc = subprocess.run(
        [
            sys.executable,
            "tools/infra/gepa_agent_message_observer.py",
            "--ledger-dir",
            str(ledger_dir),
            "--output-dir",
            str(out_dir),
            "--review-dir",
            str(review_dir),
            "--no-legacy-artifacts",
            "--no-gepa-cache",
            "--json",
        ],
        text=True,
        capture_output=True,
        check=True,
    )
    report = json.loads(proc.stdout)
    assert report["observation_count"] == 1
    assert report["scored_observation_count"] == 1
    assert report["channels"] == {"cli_channel": 1}
    assert report["thermodynamic_score"]["success_rate"] == 1.0
    assert Path(report["observations_jsonl"]).exists()
    assert Path(report["report_json"]).exists()
    assert Path(report["review_packet"]).exists()
