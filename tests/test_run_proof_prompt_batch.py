from pathlib import Path

from tools.infra.run_proof_prompt_batch import (
    assess_output_quality,
    backend_defaults,
    build_result_payload,
    extract_completion_text,
)


def test_extract_completion_text_prefers_message_content():
    response = {
        "choices": [
            {
                "message": {
                    "content": "Minimal dependency chain\n1. lemma_a\n2. lemma_b",
                    "reasoning_content": "draft reasoning",
                }
            }
        ]
    }

    assert extract_completion_text(response) == "Minimal dependency chain\n1. lemma_a\n2. lemma_b"


def test_extract_completion_text_falls_back_to_reasoning_content():
    response = {
        "choices": [
            {
                "message": {
                    "content": "",
                    "reasoning_content": "Owner / translator split\n- owner\n- translator",
                }
            }
        ]
    }

    assert extract_completion_text(response) == "Owner / translator split\n- owner\n- translator"


def test_backend_defaults_for_openai():
    defaults = backend_defaults("openai")

    assert defaults["model"] == "deepseek-prover-v2-7b-q8_0.gguf"
    assert defaults["base_url"] == "http://127.0.0.1:30002/v1"


def test_backend_defaults_for_copilot():
    defaults = backend_defaults("copilot")

    assert defaults["model"] == "gpt-4.1"
    assert defaults["base_url"] == "copilot-cli"


def test_assess_output_quality_accepts_structured_proof_reconstruction():
    text = (
        "Minimal dependency chain\n"
        "1. lemma_a\n2. lemma_b\n\n"
        "Owner / translator / coherence role split\n"
        "- owner\n- translator\n\n"
        "Proof reconstruction\n"
        "This theorem follows by rewriting through the owner lemma and then applying the bridge lemma.\n\n"
        "Nearby but unused lemma note\n"
        "- lemma_c"
    )

    verdict = assess_output_quality(text)

    assert verdict["quality"] == "acceptable"
    assert verdict["rerun_recommended"] is False


def test_assess_output_quality_flags_repetitive_low_value_output():
    text = (
        "### Formalization candidates\n\n"
        "1. theorem_a\n2. theorem_b\n\n"
        "### Proof-specialist lane\n\n"
        "The proof-specialist lane is the file.\n\n"
        "### Formalization candidates\n\n"
        "1. theorem_a\n2. theorem_b\n"
    )

    verdict = assess_output_quality(text)

    assert verdict["quality"] == "weak"
    assert verdict["rerun_recommended"] is True
    assert "repetitive" in " ".join(verdict["issues"])


def test_build_result_payload_records_prompt_and_output(tmp_path: Path):
    prompt_path = tmp_path / "prompt.md"
    prompt_path.write_text("prompt text", encoding="utf-8")

    payload = build_result_payload(
        run_id="run-1",
        prompt_path=prompt_path,
        output_text="proof-specialist result",
        response={"choices": [{"message": {"content": "proof-specialist result"}}]},
        model="gpt-4.1",
        base_url="copilot-cli",
        backend="copilot",
    )

    assert payload["schema"] == "info_geometry.proof_prompt_result.v1"
    assert payload["run_id"] == "run-1"
    assert payload["prompt_path"] == str(prompt_path)
    assert payload["output_text"] == "proof-specialist result"
    assert payload["model"] == "gpt-4.1"
    assert payload["backend"] == "copilot"
