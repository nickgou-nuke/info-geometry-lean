import json
import stat
from pathlib import Path

from tools.infra.check_vllm_mistral_compat import check_compat


def make_fake_vllm(path: Path, help_text: str) -> Path:
    script = path / "vllm"
    script.write_text(f"#!/usr/bin/env bash\necho {json.dumps(help_text)}\n", encoding="utf-8")
    script.chmod(script.stat().st_mode | stat.S_IXUSR)
    return script


def test_check_compat_passes_when_required_flags_exist(tmp_path: Path) -> None:
    fake = make_fake_vllm(
        tmp_path,
        "--tool-call-parser --enable-auto-tool-choice --reasoning-parser --attention-backend --kv-cache-dtype",
    )
    report = check_compat(vllm_bin=str(fake), timeout=5)
    assert report["ok"] is True
    assert report["required_flags"]["--reasoning-parser"] is True


def test_check_compat_fails_when_required_flags_missing(tmp_path: Path) -> None:
    fake = make_fake_vllm(tmp_path, "--attention-backend")
    report = check_compat(vllm_bin=str(fake), timeout=5)
    assert report["ok"] is False
    assert report["required_flags"]["--tool-call-parser"] is False
    assert report["warnings"]


def test_check_compat_reports_vllm_source_markers(tmp_path: Path) -> None:
    fake = make_fake_vllm(
        tmp_path,
        "--tool-call-parser --enable-auto-tool-choice --reasoning-parser --attention-backend --kv-cache-dtype",
    )
    source_root = tmp_path / "vllm_src"
    source_root.mkdir()
    (source_root / "mistral_bits.py").write_text(
        "MistralToolParser\n"
        "adjust_request\n"
        "MistralGrammarFactory\n"
        "structured_outputs\n"
        "model_can_reason\n",
        encoding="utf-8",
    )

    report = check_compat(vllm_bin=str(fake), timeout=5, vllm_source_root=source_root)

    assert report["ok"] is True
    assert report["source_markers"]["available"] is True
    assert report["source_markers"]["markers"]["grammar_injection_pr_38150"]["MistralGrammarFactory"] is True
    assert report["source_markers"]["markers"]["serving_layer_pr_39217"]["model_can_reason"] is True
