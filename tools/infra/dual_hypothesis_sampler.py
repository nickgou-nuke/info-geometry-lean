#!/usr/bin/env python3
from __future__ import annotations

import argparse
import hashlib
import json
import random
import re
import subprocess
import sys
from dataclasses import dataclass
from datetime import datetime, timezone
from pathlib import Path
from typing import Any
from urllib.error import HTTPError, URLError
from urllib.request import Request, urlopen


REPO_ROOT = Path(__file__).resolve().parents[2]


def _utc_now() -> str:
    return datetime.now(timezone.utc).isoformat()


def _stamp() -> str:
    return datetime.now(timezone.utc).strftime("%Y%m%dT%H%M%SZ")


def _slug(text: str) -> str:
    s = re.sub(r"[^a-zA-Z0-9]+", "-", text.strip().lower()).strip("-")
    return s[:96] or "goal"


def _tokenize(text: str) -> list[str]:
    return re.findall(r"[A-Za-z0-9_]+", text.lower())


def _safe_read(path: Path, *, max_chars: int) -> str:
    try:
        text = path.read_text(encoding="utf-8", errors="ignore")
    except Exception:
        return ""
    text = text.strip()
    if max_chars > 3 and len(text) > max_chars:
        text = text[: max_chars - 3] + "..."
    return text


def _extract_lean_code(text: str) -> str:
    blocks = re.findall(r"```(?:lean4?|Lean4?|LEAN4?)?\s*\n(.*?)```", text, flags=re.DOTALL)
    if blocks:
        return blocks[0].strip()
    blocks_any = re.findall(r"```[^\n]*\n(.*?)```", text, flags=re.DOTALL)
    if blocks_any:
        return blocks_any[0].strip()
    return ""


def _json_post(url: str, payload: dict[str, Any], *, api_key: str, timeout_sec: int) -> dict[str, Any]:
    data = json.dumps(payload, ensure_ascii=True).encode("utf-8")
    req = Request(url, data=data, method="POST")
    req.add_header("Content-Type", "application/json")
    req.add_header("Accept", "application/json")
    req.add_header("Authorization", f"Bearer {api_key}")
    try:
        with urlopen(req, timeout=timeout_sec) as resp:
            raw = resp.read().decode("utf-8")
            return json.loads(raw) if raw else {}
    except HTTPError as exc:
        body = exc.read().decode("utf-8", errors="replace")
        raise RuntimeError(f"HTTP {exc.code} {url}: {body}") from exc
    except URLError as exc:
        raise RuntimeError(f"Network error for {url}: {exc}") from exc


def _normalize_chat_base_url(base_url: str) -> str:
    s = base_url.strip().rstrip("/")
    if s.endswith("/v1"):
        return s + "/chat/completions"
    if s.endswith("/chat/completions"):
        return s
    return s + "/v1/chat/completions"


def _chat_completion(
    *,
    base_url: str,
    api_key: str,
    model: str,
    messages: list[dict[str, str]],
    temperature: float,
    max_tokens: int,
    timeout_sec: int,
) -> tuple[str, dict[str, Any]]:
    url = _normalize_chat_base_url(base_url)
    payload = {
        "model": model,
        "messages": messages,
        "temperature": float(temperature),
        "max_tokens": int(max_tokens),
    }
    raw = _json_post(url, payload, api_key=api_key, timeout_sec=timeout_sec)
    choices = raw.get("choices", [])
    if not isinstance(choices, list) or not choices:
        raise RuntimeError(f"empty choices from {url}")
    first = choices[0] if isinstance(choices[0], dict) else {}
    msg = first.get("message", {})
    if not isinstance(msg, dict):
        msg = {}
    content = str(msg.get("content", "")).strip()
    if not content:
        raise RuntimeError(f"empty response content from {url}")
    usage = raw.get("usage")
    usage_obj = usage if isinstance(usage, dict) else {}
    return content, usage_obj


def _sanitize_gemini_args(raw_args: list[str]) -> tuple[list[str], list[str]]:
    """Drop legacy cache-retention args unsupported by current backends."""
    sanitized: list[str] = []
    dropped: list[str] = []
    skip_next = False
    for idx, arg in enumerate(raw_args):
        if skip_next:
            skip_next = False
            continue
        if "prompt_cache_retention" not in arg:
            sanitized.append(arg)
            continue

        dropped.append(arg)
        if arg.strip() == "--prompt_cache_retention" and idx + 1 < len(raw_args):
            dropped.append(raw_args[idx + 1])
            skip_next = True
    return sanitized, dropped


def _messages_to_prompt(messages: list[dict[str, str]]) -> str:
    parts: list[str] = []
    for msg in messages:
        role = str(msg.get("role", "user")).strip().upper() or "USER"
        content = str(msg.get("content", "")).strip()
        if not content:
            continue
        parts.append(f"{role}:\n{content}")
    parts.append("Return plain text with one Lean code block fenced as ```lean ... ```.")
    return "\n\n".join(parts).strip()


def _gemini_cli_completion(
    *,
    gemini_bin: str,
    gemini_args: list[str],
    input_mode: str,
    prompt_flag: str,
    messages: list[dict[str, str]],
    timeout_sec: int,
) -> tuple[str, dict[str, Any]]:
    prompt = _messages_to_prompt(messages)
    cmd = [gemini_bin] + gemini_args
    try:
        if input_mode == "arg":
            cmd = cmd + [prompt_flag, prompt]
            proc = subprocess.run(
                cmd,
                text=True,
                capture_output=True,
                timeout=max(10, int(timeout_sec)),
                check=False,
            )
        else:
            proc = subprocess.run(
                cmd,
                input=prompt,
                text=True,
                capture_output=True,
                timeout=max(10, int(timeout_sec)),
                check=False,
            )
    except subprocess.TimeoutExpired:
        raise RuntimeError(f"Gemini CLI timeout after {timeout_sec}s")
    except Exception as exc:
        raise RuntimeError(f"Gemini CLI invocation failed: {exc}") from exc

    stdout = (proc.stdout or "").strip()
    stderr = (proc.stderr or "").strip()
    if proc.returncode != 0:
        raise RuntimeError(f"Gemini CLI error code={proc.returncode}: {stderr or 'no stderr'}")
    if not stdout:
        raise RuntimeError("Gemini CLI returned empty output")
    return stdout, {"provider": "gemini-cli", "returncode": int(proc.returncode)}


@dataclass(frozen=True)
class ContextChunk:
    source: str
    text: str


def _load_black_books(goal: str, *, glob_pattern: str, limit: int, max_chars_per_file: int) -> list[ContextChunk]:
    root = REPO_ROOT
    files = sorted(root.glob(glob_pattern))
    if not files:
        return []
    goal_tokens = set(_tokenize(goal))
    scored: list[tuple[int, Path, str]] = []
    for path in files:
        text = _safe_read(path, max_chars=max_chars_per_file)
        if not text:
            continue
        toks = set(_tokenize(text))
        score = len(goal_tokens & toks)
        scored.append((score, path, text))
    if not scored:
        return []
    scored.sort(key=lambda x: (x[0], str(x[1])), reverse=True)
    out: list[ContextChunk] = []
    for _, path, text in scored[: max(0, limit)]:
        out.append(ContextChunk(source=str(path.resolve()), text=text))
    return out


def _load_context_files(paths: list[str], *, max_chars_per_file: int) -> list[ContextChunk]:
    out: list[ContextChunk] = []
    for raw in paths:
        p = Path(raw).resolve()
        if not p.exists():
            continue
        text = _safe_read(p, max_chars=max_chars_per_file)
        if not text:
            continue
        out.append(ContextChunk(source=str(p), text=text))
    return out


def _load_dag_context(path: str, *, top_k: int) -> list[ContextChunk]:
    p = Path(path).resolve()
    if not p.exists():
        return []
    try:
        payload = json.loads(p.read_text(encoding="utf-8"))
    except Exception:
        return []
    rows = payload.get("top_candidates", [])
    if not isinstance(rows, list):
        return []
    lines: list[str] = []
    for row in rows[: max(0, top_k)]:
        if not isinstance(row, dict):
            continue
        src = row.get("source", {})
        tgt = row.get("target", {})
        src_name = str(src.get("name", "")).strip() if isinstance(src, dict) else ""
        tgt_name = str(tgt.get("name", "")).strip() if isinstance(tgt, dict) else ""
        score = row.get("scorer", {}).get("score", 0.0) if isinstance(row.get("scorer"), dict) else 0.0
        kind = str(row.get("link_kind", "")).strip()
        if src_name or tgt_name:
            lines.append(f"- {src_name} -> {tgt_name} [{kind}] score={score}")
    if not lines:
        return []
    return [ContextChunk(source=str(p), text="DAG top candidates:\n" + "\n".join(lines))]


def _build_messages(goal: str, chunks: list[ContextChunk], *, rng: random.Random) -> list[dict[str, str]]:
    context_sections = []
    shuffled = chunks[:]
    rng.shuffle(shuffled)
    for idx, chunk in enumerate(shuffled, start=1):
        context_sections.append(f"[Context {idx}] source={chunk.source}\n{chunk.text}")
    context_blob = "\n\n".join(context_sections) if context_sections else "No external context provided."
    system = (
        "You are a Lean 4 proof hypothesis generator for a nonstandard repository. "
        "Do not normalize unusual axioms/lemmas away. Produce a concrete candidate theorem or lemma and Lean 4 sketch."
    )
    user = (
        f"Goal:\n{goal}\n\n"
        "Repository context:\n"
        f"{context_blob}\n\n"
        "Return:\n"
        "1) concise hypothesis statement\n"
        "2) rationale for nonstandard links\n"
        "3) Lean 4 code block (```lean ... ```), even if incomplete.\n"
    )
    return [{"role": "system", "content": system}, {"role": "user", "content": user}]


def parse_args() -> argparse.Namespace:
    ap = argparse.ArgumentParser(
        description=(
            "Sample Lean4 hypotheses from base+tuned models using repo-local context "
            "(DAG + black books + optional files)."
        )
    )
    ap.add_argument("--goal", default="", help="Goal text. Required unless --goal-file is set.")
    ap.add_argument("--goal-file", default="", help="Optional file with goal text.")
    ap.add_argument("--context-file", action="append", default=[], help="Additional context file path (repeatable).")
    ap.add_argument("--dag-context", default="", help="Optional rerank report JSON path for DAG context.")
    ap.add_argument("--dag-top-k", type=int, default=12)
    ap.add_argument("--black-book-glob", default="docs/black_books/*.md")
    ap.add_argument("--black-book-limit", type=int, default=3)
    ap.add_argument("--max-context-chars-per-file", type=int, default=2400)

    ap.add_argument("--base-url-base", default="http://127.0.0.1:8000/v1")
    ap.add_argument("--model-base", default="qwen3-proposer")
    ap.add_argument("--api-key-base", default="EMPTY")
    ap.add_argument("--provider-base", choices=["openai-chat", "gemini-cli"], default="openai-chat")
    ap.add_argument("--gemini-bin-base", default="gemini")
    ap.add_argument("--gemini-arg-base", action="append", default=[])
    ap.add_argument("--gemini-input-mode-base", choices=["stdin", "arg"], default="stdin")
    ap.add_argument("--gemini-prompt-flag-base", default="-p")
    ap.add_argument("--samples-base", type=int, default=4)
    ap.add_argument("--temperature-base", type=float, default=0.95)

    ap.add_argument("--base-url-tuned", default="http://127.0.0.1:8000/v1")
    ap.add_argument("--model-tuned", default="deepseek-formalizer")
    ap.add_argument("--api-key-tuned", default="EMPTY")
    ap.add_argument("--provider-tuned", choices=["openai-chat", "gemini-cli"], default="openai-chat")
    ap.add_argument("--gemini-bin-tuned", default="gemini")
    ap.add_argument("--gemini-arg-tuned", action="append", default=[])
    ap.add_argument("--gemini-input-mode-tuned", choices=["stdin", "arg"], default="stdin")
    ap.add_argument("--gemini-prompt-flag-tuned", default="-p")
    ap.add_argument("--samples-tuned", type=int, default=4)
    ap.add_argument("--temperature-tuned", type=float, default=0.55)

    ap.add_argument("--max-tokens", type=int, default=1600)
    ap.add_argument("--timeout-sec", type=int, default=120)
    ap.add_argument("--seed", type=int, default=20260418)
    ap.add_argument("--dry-run", action="store_true")

    ap.add_argument("--out", default="")
    ap.add_argument("--manifest-out", default="")
    return ap.parse_args()


def main() -> int:
    args = parse_args()
    rng = random.Random(args.seed)

    goal = args.goal.strip()
    if args.goal_file:
        goal_path = Path(args.goal_file).resolve()
        if not goal_path.exists():
            raise FileNotFoundError(f"goal file not found: {goal_path}")
        goal = _safe_read(goal_path, max_chars=20000).strip()
    if not goal:
        raise SystemExit("goal is required (set --goal or --goal-file)")

    run_id = _stamp()
    out = Path(args.out).resolve() if args.out else (REPO_ROOT / "reports" / "training" / "hypothesis" / f"{run_id}-{_slug(goal)}.jsonl")
    manifest_out = (
        Path(args.manifest_out).resolve()
        if args.manifest_out
        else (REPO_ROOT / "reports" / "training" / "hypothesis" / f"{run_id}-{_slug(goal)}.manifest.json")
    )

    chunks: list[ContextChunk] = []
    chunks.extend(_load_context_files(args.context_file, max_chars_per_file=max(128, args.max_context_chars_per_file)))
    if args.dag_context:
        chunks.extend(_load_dag_context(args.dag_context, top_k=max(0, args.dag_top_k)))
    chunks.extend(
        _load_black_books(
            goal,
            glob_pattern=args.black_book_glob,
            limit=max(0, args.black_book_limit),
            max_chars_per_file=max(128, args.max_context_chars_per_file),
        )
    )
    messages = _build_messages(goal, chunks, rng=rng)
    prompt_hash = hashlib.sha1(json.dumps(messages, ensure_ascii=True, sort_keys=True).encode("utf-8")).hexdigest()

    out.parent.mkdir(parents=True, exist_ok=True)
    rows: list[dict[str, Any]] = []

    gemini_args_base, dropped_base = _sanitize_gemini_args(args.gemini_arg_base)
    gemini_args_tuned, dropped_tuned = _sanitize_gemini_args(args.gemini_arg_tuned)
    if dropped_base:
        print(
            "warning: dropped unsupported --gemini-arg-base entries containing "
            "'prompt_cache_retention': " + ", ".join(dropped_base),
            file=sys.stderr,
        )
    if dropped_tuned:
        print(
            "warning: dropped unsupported --gemini-arg-tuned entries containing "
            "'prompt_cache_retention': " + ", ".join(dropped_tuned),
            file=sys.stderr,
        )

    model_jobs = [
        {
            "role": "base",
            "provider": args.provider_base,
            "base_url": args.base_url_base,
            "api_key": args.api_key_base,
            "model": args.model_base,
            "gemini_bin": args.gemini_bin_base,
            "gemini_args": gemini_args_base,
            "gemini_input_mode": args.gemini_input_mode_base,
            "gemini_prompt_flag": args.gemini_prompt_flag_base,
            "samples": max(0, int(args.samples_base)),
            "temperature": float(args.temperature_base),
        },
        {
            "role": "tuned",
            "provider": args.provider_tuned,
            "base_url": args.base_url_tuned,
            "api_key": args.api_key_tuned,
            "model": args.model_tuned,
            "gemini_bin": args.gemini_bin_tuned,
            "gemini_args": gemini_args_tuned,
            "gemini_input_mode": args.gemini_input_mode_tuned,
            "gemini_prompt_flag": args.gemini_prompt_flag_tuned,
            "samples": max(0, int(args.samples_tuned)),
            "temperature": float(args.temperature_tuned),
        },
    ]

    with out.open("w", encoding="utf-8") as handle:
        for job in model_jobs:
            for idx in range(1, int(job["samples"]) + 1):
                hyp_key = f"{run_id}|{job['role']}|{idx}"
                hyp_hash = hashlib.sha1(hyp_key.encode("utf-8")).hexdigest()[:10]
                hypothesis_id = f"hyp_{job['role']}_{idx}_{hyp_hash}"
                row: dict[str, Any] = {
                    "schema": "lean.hypothesis.candidate.v1",
                    "hypothesis_id": hypothesis_id,
                    "created_at": _utc_now(),
                    "run_id": run_id,
                    "goal": goal,
                    "model_role": job["role"],
                    "provider": str(job["provider"]),
                    "model": str(job["model"]),
                    "base_url": str(job["base_url"]),
                    "sample_index": idx,
                    "temperature": float(job["temperature"]),
                    "prompt_hash": prompt_hash,
                    "context_sources": [c.source for c in chunks],
                    "status": "ok",
                }
                if args.dry_run:
                    mock = (
                        f"Hypothesis ({job['role']} #{idx}): nonstandard bridge around `{_slug(goal)}`.\n\n"
                        "```lean\n"
                        "import InfoGeometry.All\n\n"
                        "theorem generated_hypothesis_placeholder : True := by\n"
                        "  trivial\n"
                        "```\n"
                    )
                    row["response"] = mock
                    row["usage"] = {}
                else:
                    try:
                        provider = str(job.get("provider", "openai-chat")).strip()
                        if provider == "openai-chat":
                            text, usage = _chat_completion(
                                base_url=str(job["base_url"]),
                                api_key=str(job["api_key"]),
                                model=str(job["model"]),
                                messages=messages,
                                temperature=float(job["temperature"]),
                                max_tokens=max(64, int(args.max_tokens)),
                                timeout_sec=max(10, int(args.timeout_sec)),
                            )
                        elif provider == "gemini-cli":
                            text, usage = _gemini_cli_completion(
                                gemini_bin=str(job.get("gemini_bin", "gemini")),
                                gemini_args=list(job.get("gemini_args", [])),
                                input_mode=str(job.get("gemini_input_mode", "stdin")),
                                prompt_flag=str(job.get("gemini_prompt_flag", "-p")),
                                messages=messages,
                                timeout_sec=max(10, int(args.timeout_sec)),
                            )
                        else:
                            raise RuntimeError(f"unsupported provider: {provider}")
                        row["response"] = text
                        row["usage"] = usage
                    except Exception as exc:
                        row["status"] = "error"
                        row["error"] = str(exc)
                        row["response"] = ""
                        row["usage"] = {}

                lean_code = _extract_lean_code(str(row.get("response", "")))
                row["lean_code"] = lean_code
                row["has_lean_code"] = bool(lean_code.strip())
                handle.write(json.dumps(row, ensure_ascii=True) + "\n")
                rows.append(row)

    success_rows = [r for r in rows if r.get("status") == "ok"]
    manifest = {
        "schema": "lean.hypothesis.sampler.manifest.v1",
        "run_id": run_id,
        "created_at": _utc_now(),
        "goal": goal,
        "prompt_hash": prompt_hash,
        "out": str(out),
        "dry_run": bool(args.dry_run),
        "counts": {
            "total": len(rows),
            "ok": len(success_rows),
            "error": len(rows) - len(success_rows),
            "with_lean_code": sum(1 for r in rows if bool(r.get("has_lean_code"))),
        },
        "models": [
            {
                "role": j["role"],
                "provider": j["provider"],
                "model": j["model"],
                "base_url": j["base_url"],
                "gemini_bin": j["gemini_bin"] if j["provider"] == "gemini-cli" else "",
                "gemini_args": j["gemini_args"] if j["provider"] == "gemini-cli" else [],
                "samples": j["samples"],
                "temperature": j["temperature"],
            }
            for j in model_jobs
        ],
        "context_sources": [c.source for c in chunks],
    }
    manifest_out.parent.mkdir(parents=True, exist_ok=True)
    manifest_out.write_text(json.dumps(manifest, indent=2, ensure_ascii=True) + "\n", encoding="utf-8")

    print(f"hypothesis candidates: {out}")
    print(f"sampler manifest:      {manifest_out}")
    print(
        f"counts: total={manifest['counts']['total']} "
        f"ok={manifest['counts']['ok']} "
        f"errors={manifest['counts']['error']} "
        f"with_lean_code={manifest['counts']['with_lean_code']}"
    )
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
