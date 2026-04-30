#!/usr/bin/env python3
from __future__ import annotations

import argparse
import json
import subprocess
import sys
from datetime import datetime, timezone
from pathlib import Path
from typing import Any

REPO_ROOT = Path(__file__).resolve().parents[2]
if str(REPO_ROOT) not in sys.path:
    sys.path.insert(0, str(REPO_ROOT))

from tools.infra.hermes_bounded_runner import call_openai_compatible

DEFAULT_OPENAI_BASE_URL = "http://127.0.0.1:8001/v1"
DEFAULT_OPENAI_MODEL = "deepseek-prover-v2-7b"
DEFAULT_API_KEY = "***"
DEFAULT_COPILOT_MODEL = "gpt-4.1"
PROMPT_DIR = REPO_ROOT / "artifacts" / "hermes_loop" / "proof_prompts"
RESULT_DIR = REPO_ROOT / "artifacts" / "hermes_loop" / "proof_results"
QUALITY_REQUIRED_MARKERS = [
    "minimal dependency chain",
    "proof reconstruction",
]
WEAK_OUTPUT_PATTERNS = [
    "formalization candidates",
    "proof-specialist lane",
]


def utc_now() -> str:
    return datetime.now(timezone.utc).isoformat()


def backend_defaults(backend: str) -> dict[str, str]:
    if backend == "copilot":
        return {"model": DEFAULT_COPILOT_MODEL, "base_url": "copilot-cli"}
    if backend == "openai":
        return {"model": DEFAULT_OPENAI_MODEL, "base_url": DEFAULT_OPENAI_BASE_URL}
    raise ValueError(f"unsupported backend: {backend}")


def extract_completion_text(response: dict[str, Any]) -> str:
    choices = response.get("choices") or []
    if not choices:
        return ""
    message = choices[0].get("message") or {}
    content = message.get("content")
    if isinstance(content, str) and content.strip():
        return content.strip()
    reasoning = message.get("reasoning_content")
    if isinstance(reasoning, str) and reasoning.strip():
        return reasoning.strip()
    return ""


def assess_output_quality(output_text: str) -> dict[str, Any]:
    text = output_text.strip()
    lowered = text.lower()
    issues: list[str] = []
    missing = [marker for marker in QUALITY_REQUIRED_MARKERS if marker not in lowered]
    if missing:
        issues.append(f"missing required markers: {', '.join(missing)}")
    repetitive_hits = [pattern for pattern in WEAK_OUTPUT_PATTERNS if lowered.count(pattern) >= 2]
    if repetitive_hits:
        issues.append(f"repetitive low-value sections: {', '.join(repetitive_hits)}")
    return {
        "quality": "acceptable" if not issues else "weak",
        "issues": issues,
        "rerun_recommended": bool(issues),
    }


def build_result_payload(
    *,
    run_id: str,
    prompt_path: Path,
    output_text: str,
    response: dict[str, Any],
    model: str,
    base_url: str,
    backend: str,
) -> dict[str, Any]:
    return {
        "schema": "info_geometry.proof_prompt_result.v1",
        "run_id": run_id,
        "created_at": utc_now(),
        "prompt_path": str(prompt_path),
        "backend": backend,
        "model": model,
        "base_url": base_url,
        "output_text": output_text,
        "quality": assess_output_quality(output_text),
        "raw_response": response,
    }


def write_json(path: Path, payload: Any) -> None:
    path.parent.mkdir(parents=True, exist_ok=True)
    path.write_text(json.dumps(payload, indent=2, ensure_ascii=False) + "\n", encoding="utf-8")


def write_markdown(path: Path, prompt_path: Path, prompt_text: str, output_text: str) -> None:
    path.parent.mkdir(parents=True, exist_ok=True)
    path.write_text(
        "\n".join(
            [
                f"# Proof Prompt Result: {prompt_path.stem}",
                "",
                f"Source prompt: {prompt_path}",
                "",
                "## Output",
                "",
                output_text or "(empty response)",
                "",
                "## Prompt",
                "",
                "```text",
                prompt_text,
                "```",
                "",
            ]
        ),
        encoding="utf-8",
    )


def run_openai_prompt(
    prompt_text: str,
    *,
    base_url: str,
    model: str,
    api_key: str,
    timeout: int,
    max_tokens: int,
) -> dict[str, Any]:
    return call_openai_compatible(
        base_url=base_url,
        model=model,
        api_key=api_key,
        prompt=prompt_text,
        timeout=timeout,
        max_tokens=max_tokens,
    )


def run_copilot_prompt(prompt_text: str, *, model: str, timeout: int, workdir: Path) -> dict[str, Any]:
    cmd = [
        "copilot",
        "-p",
        prompt_text,
        "--model",
        model,
        "--allow-all-tools",
        "--output-format",
        "text",
    ]
    proc = subprocess.run(
        cmd,
        cwd=workdir,
        text=True,
        capture_output=True,
        timeout=timeout,
        check=False,
    )
    text = (proc.stdout or "").strip()
    if proc.returncode != 0:
        raise RuntimeError((proc.stderr or proc.stdout or f"copilot exit {proc.returncode}").strip())
    return {
        "choices": [{"message": {"content": text}}],
        "backend": "copilot-cli",
    }


def run_prompt(
    prompt_path: Path,
    *,
    backend: str,
    base_url: str,
    model: str,
    api_key: str,
    timeout: int,
    max_tokens: int,
) -> Path:
    prompt_text = prompt_path.read_text(encoding="utf-8")
    if backend == "copilot":
        response = run_copilot_prompt(prompt_text, model=model, timeout=timeout, workdir=REPO_ROOT)
    else:
        response = run_openai_prompt(
            prompt_text,
            base_url=base_url,
            model=model,
            api_key=api_key,
            timeout=timeout,
            max_tokens=max_tokens,
        )
    output_text = extract_completion_text(response)
    stamp = datetime.now(timezone.utc).strftime("%Y%m%dT%H%M%SZ")
    run_id = f"{stamp}-{prompt_path.stem}"
    json_path = RESULT_DIR / f"{run_id}.json"
    md_path = RESULT_DIR / f"{run_id}.md"
    payload = build_result_payload(
        run_id=run_id,
        prompt_path=prompt_path,
        output_text=output_text,
        response=response,
        model=model,
        base_url=base_url,
        backend=backend,
    )
    write_json(json_path, payload)
    write_markdown(md_path, prompt_path, prompt_text, output_text)
    write_json(RESULT_DIR / f"{prompt_path.stem}.latest.json", payload)
    write_markdown(RESULT_DIR / f"{prompt_path.stem}.latest.md", prompt_path, prompt_text, output_text)
    return json_path


def parse_args() -> argparse.Namespace:
    parser = argparse.ArgumentParser(description="Run proof-specialist prompts against the configured proof lane.")
    parser.add_argument("--prompt", type=Path, help="Specific prompt markdown file to run.")
    parser.add_argument("--prompt-dir", type=Path, default=PROMPT_DIR)
    parser.add_argument("--backend", choices=["openai", "copilot"], default="copilot")
    parser.add_argument("--base-url", default="")
    parser.add_argument("--model", default="")
    parser.add_argument("--api-key", default=DEFAULT_API_KEY)
    parser.add_argument("--timeout", type=int, default=180)
    parser.add_argument("--max-tokens", type=int, default=1200)
    return parser.parse_args()


def main() -> int:
    args = parse_args()
    defaults = backend_defaults(args.backend)
    base_url = args.base_url or defaults["base_url"]
    model = args.model or defaults["model"]
    prompt_paths = [args.prompt] if args.prompt else sorted(args.prompt_dir.glob("*.md"))
    if not prompt_paths:
        print("no proof prompts found")
        return 0
    for prompt_path in prompt_paths:
        out = run_prompt(
            prompt_path,
            backend=args.backend,
            base_url=base_url,
            model=model,
            api_key=args.api_key,
            timeout=args.timeout,
            max_tokens=args.max_tokens,
        )
        print(out)
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
