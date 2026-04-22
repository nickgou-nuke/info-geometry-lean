from pathlib import Path

from tools.infra.run_copilot_codex_lean_pipeline import (
    build_codex_prompt,
    build_pipeline_payload,
)


def test_build_codex_prompt_mentions_copilot_and_lean_verification_paths():
    prompt = build_codex_prompt(
        packet_id="repo-softmax-variance-corridor-002",
        prompt_text="proof prompt body",
        copilot_output="candidate theorem sketch",
        lean_module="InfoGeometry.ExponentialFamily.Analytic.Softmax",
        lean_file=Path("lean/InfoGeometry/ExponentialFamily/Analytic/Softmax.lean"),
    )

    assert "candidate theorem sketch" in prompt
    assert "InfoGeometry.ExponentialFamily.Analytic.Softmax" in prompt
    assert "lean/InfoGeometry/ExponentialFamily/Analytic/Softmax.lean" in prompt
    assert "lake build InfoGeometry.ExponentialFamily.Analytic.Softmax" in prompt
    assert "lean_interact_wrapper.py" in prompt


def test_build_pipeline_payload_records_stage_artifacts(tmp_path: Path):
    prompt_path = tmp_path / "prompt.md"
    prompt_path.write_text("prompt", encoding="utf-8")
    payload = build_pipeline_payload(
        run_id="run-1",
        packet_id="repo-softmax-variance-corridor-002",
        prompt_path=prompt_path,
        copilot_output="candidate theorem sketch",
        codex_prompt_path=tmp_path / "codex_prompt.md",
        lean_module="InfoGeometry.ExponentialFamily.Analytic.Softmax",
        lean_file=Path("lean/InfoGeometry/ExponentialFamily/Analytic/Softmax.lean"),
        codex_executed=False,
    )

    assert payload["schema"] == "info_geometry.copilot_codex_lean_pipeline.v1"
    assert payload["packet_id"] == "repo-softmax-variance-corridor-002"
    assert payload["stages"]["copilot"]["output_text"] == "candidate theorem sketch"
    assert payload["stages"]["codex"]["executed"] is False
    assert payload["stages"]["lean"]["module"] == "InfoGeometry.ExponentialFamily.Analytic.Softmax"
