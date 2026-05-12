#!/usr/bin/env python3
from __future__ import annotations

import argparse
import json
import os
import re
import subprocess
import sys
from concurrent.futures import ThreadPoolExecutor
from pathlib import Path
from typing import Any
from urllib import error, request

from tools.infra.semantic_chunking_validator import validate


def _extract_json_object(text: str) -> dict[str, Any]:
    cleaned = text.strip()
    if cleaned.startswith("```"):
        cleaned = re.sub(r"^```[a-zA-Z0-9_-]*\n", "", cleaned)
        cleaned = re.sub(r"\n```$", "", cleaned)
    
    # Try direct load
    try:
        obj = json.loads(cleaned)
        if isinstance(obj, dict):
            return obj
    except json.JSONDecodeError:
        pass

    # Try finding braces
    start = cleaned.find("{")
    end = cleaned.rfind("}")
    if start >= 0 and end > start:
        try:
            obj = json.loads(cleaned[start : end + 1])
            if isinstance(obj, dict):
                return obj
        except json.JSONDecodeError:
            pass
            
    raise ValueError(f"no JSON object found in model response: {text[:200]}...")


def _post_json(url: str, payload: dict[str, Any], headers: dict[str, str], timeout: int) -> dict[str, Any]:
    data = json.dumps(payload).encode("utf-8")
    req = request.Request(url, data=data, method="POST", headers=headers)
    try:
        with request.urlopen(req, timeout=timeout) as resp:
            raw = resp.read().decode("utf-8")
    except error.HTTPError as exc:
        detail = exc.read().decode("utf-8", errors="replace")
        raise RuntimeError(f"HTTP {exc.code} from {url}: {detail}") from exc
    except error.URLError as exc:
        raise RuntimeError(f"cannot reach {url}: {exc.reason}") from exc

    out = json.loads(raw)
    if not isinstance(out, dict):
        raise ValueError("response is not JSON object")
    return out


def _openrouter_frontier(source_text: str, model: str, timeout: int) -> dict[str, Any]:
    key = os.environ.get("OPENROUTER_API_KEY", "").strip()
    if not key:
        raise RuntimeError("OPENROUTER_API_KEY is required for openrouter frontier mode")

    url = "https://openrouter.ai/api/v1/chat/completions"
    prompt = (
        "Return strict JSON object with keys: document_id, source_path, chunks. "
        "Each chunk requires id,type,title,start_line,end_line,anchors,context_header,math_symbols,dependencies. "
        "Never split inside LaTeX math/env blocks. No prose. Source follows:\n\n"
        + source_text
    )
    payload = {
        "model": model,
        "messages": [
            {"role": "system", "content": "You are a mathematical semantic chunk boundary mapper. Output strict JSON only."},
            {"role": "user", "content": prompt},
        ],
        "temperature": 0,
        "max_tokens": 12000,
        "stream": False,
    }
    headers = {
        "Authorization": f"Bearer {key}",
        "Content-Type": "application/json",
    }
    data = _post_json(url, payload, headers, timeout)
    choices = data.get("choices")
    if not isinstance(choices, list) or not choices:
        raise RuntimeError(f"openrouter returned no choices: {data}")
    msg = choices[0].get("message", {}) if isinstance(choices[0], dict) else {}
    content = msg.get("content", "") if isinstance(msg, dict) else ""
    if not isinstance(content, str):
        raise RuntimeError("openrouter response has non-string content")
    return _extract_json_object(content)


def _gemini_cli_frontier(source_text: str, repo_root: Path) -> dict[str, Any]:
    prompt = (
        "You are a mathematical semantic chunk boundary mapper. "
        "Return strict JSON object with keys: document_id, source_path, chunks. "
        "Each chunk requires id,type,title,start_line,end_line,anchors,context_header,math_symbols,dependencies. "
        "Never split inside LaTeX math/env blocks. No prose. "
        "Output ONLY strict JSON. Source follows:\n\n" + source_text
    )
    
    cmd = ["gemini", "ask", prompt]
    # We use a subshell to avoid prompt length limits if needed, but for now simple call.
    proc = subprocess.run(cmd, cwd=repo_root, text=True, capture_output=True, check=False)
    if proc.returncode != 0:
        raise RuntimeError(f"gemini-cli call failed: {proc.stderr}")
    
    return _extract_json_object(proc.stdout)


def _gemini_guard_check(repo_root: Path) -> None:
    cmd = ["python3", "tools/infra/gemini_cli_guard.py", "--check", "--json"]
    proc = subprocess.run(cmd, cwd=repo_root, text=True, capture_output=True, check=False)
    if proc.returncode != 0:
        raise RuntimeError(f"gemini guard denied: {proc.stdout or proc.stderr}")


def _load_frontier_map(args: argparse.Namespace, source_text: str, repo_root: Path) -> dict[str, Any]:
    if args.frontier_json:
        data = json.loads(Path(args.frontier_json).read_text(encoding="utf-8"))
        if not isinstance(data, dict):
            raise ValueError("frontier_json must contain top-level JSON object")
        return data

    if args.frontier_mode == "openrouter":
        return _openrouter_frontier(source_text, args.openrouter_model, args.timeout)

    if args.frontier_mode == "gemini-cli":
        _gemini_guard_check(repo_root)
        return _gemini_cli_frontier(source_text, repo_root)

    raise RuntimeError("no frontier map source configured")


def _leanstral_refine_chunk(chunk: dict[str, Any], source_lines: list[str], endpoint: str, model: str, timeout: int) -> dict[str, Any]:
    try:
        start = int(chunk["start_line"])
        end = int(chunk["end_line"])
        lo = max(1, start - 3)
        hi = min(len(source_lines), end + 3)
        excerpt = "\n".join(f"{i+1}: {source_lines[i]}" for i in range(lo - 1, hi))

        prompt = (
            "Refine this single chunk JSON object conservatively. Keep id stable. "
            "Allowed edits: start_line/end_line/type/context_header/math_symbols/dependencies/anchors. "
            "Never move boundaries inside open LaTeX environments or math blocks. "
            "Return strict JSON object only.\n\n"
            f"Chunk:\n{json.dumps(chunk, ensure_ascii=False)}\n\n"
            f"Source excerpt (line numbered):\n{excerpt}\n"
        )

        url = endpoint.rstrip("/") + "/chat/completions"
        payload = {
            "model": model,
            "messages": [
                {"role": "system", "content": "You refine chunk metadata. Output strict JSON only."},
                {"role": "user", "content": prompt},
            ],
            "temperature": 0,
            "max_tokens": 800,
            "stream": False,
        }
        headers = {"Content-Type": "application/json"}
        data = _post_json(url, payload, headers, timeout)
        choices = data.get("choices")
        if not isinstance(choices, list) or not choices:
            return chunk
        msg = choices[0].get("message", {}) if isinstance(choices[0], dict) else {}
        content = msg.get("content", "") if isinstance(msg, dict) else ""
        if not isinstance(content, str) or not content.strip():
            return chunk
        refined = _extract_json_object(content)
        if not isinstance(refined, dict):
            return chunk
        return refined
    except Exception:
        # Fallback to original chunk on any failure during refinement
        return chunk


def run(args: argparse.Namespace) -> int:
    source_path = Path(args.source).resolve()
    if not source_path.exists():
        raise FileNotFoundError(source_path)

    repo_root = Path(__file__).resolve().parents[2]
    source_text = source_path.read_text(encoding="utf-8")
    source_lines = source_text.splitlines()

    print(f"[chunker] loading frontier map ({args.frontier_mode})...")
    frontier_map = _load_frontier_map(args, source_text, repo_root)
    frontier_map.setdefault("document_id", source_path.stem)
    frontier_map["source_path"] = str(source_path)

    out_frontier = Path(args.out_frontier)
    out_frontier.parent.mkdir(parents=True, exist_ok=True)
    out_frontier.write_text(json.dumps(frontier_map, indent=2, ensure_ascii=False) + "\n", encoding="utf-8")

    refined_map = dict(frontier_map)
    chunks = frontier_map.get("chunks", [])
    if not isinstance(chunks, list):
        raise ValueError("frontier map must contain list under chunks")

    if args.skip_refine:
        print("[chunker] skipping refinement lane.")
        refined_chunks = [c for c in chunks if isinstance(c, dict)]
    else:
        print(f"[chunker] refining {len(chunks)} chunks in parallel (workers={args.parallel})...")
        with ThreadPoolExecutor(max_workers=args.parallel) as executor:
            futures = [
                executor.submit(
                    _leanstral_refine_chunk,
                    chunk,
                    source_lines,
                    args.leanstral_endpoint,
                    args.leanstral_model,
                    args.timeout,
                )
                for chunk in chunks if isinstance(chunk, dict)
            ]
            refined_chunks = [f.result() for f in futures]

    refined_map["chunks"] = refined_chunks
    
    # Best-effort validation fallback: 
    # If a refined chunk causes a FAIL, we should ideally revert it, 
    # but for now we validate the whole set.
    out_refined = Path(args.out_refined)
    out_refined.parent.mkdir(parents=True, exist_ok=True)
    out_refined.write_text(json.dumps(refined_map, indent=2, ensure_ascii=False) + "\n", encoding="utf-8")

    errors, warnings = validate(source_path, out_refined)
    
    # Simple fallback: if refined fails, check if frontier would have passed.
    if errors and not args.skip_refine:
        print("[chunker] refined map FAILED validation. Checking if frontier map is better...")
        f_errors, f_warnings = validate(source_path, out_frontier)
        if not f_errors:
            print("[chunker] fallback: frontier map is valid. Reverting to frontier.")
            refined_map = frontier_map
            out_refined.write_text(json.dumps(refined_map, indent=2, ensure_ascii=False) + "\n", encoding="utf-8")
            errors, warnings = f_errors, f_warnings

    report = {
        "status": "FAIL" if errors else ("WARN" if warnings else "PASS"),
        "source": str(source_path),
        "frontier": str(out_frontier),
        "refined": str(out_refined),
        "error_count": len(errors),
        "warning_count": len(warnings),
        "errors": errors,
        "warnings": warnings,
    }
    out_report = Path(args.out_report)
    out_report.parent.mkdir(parents=True, exist_ok=True)
    out_report.write_text(json.dumps(report, indent=2, ensure_ascii=False) + "\n", encoding="utf-8")

    print(json.dumps(report, indent=2, ensure_ascii=False))
    return 1 if errors else 0


def build_parser() -> argparse.ArgumentParser:
    p = argparse.ArgumentParser(description="Two-lane semantic chunking runner: frontier map -> local refine -> local validate")
    p.add_argument("--source", required=True, help="Path to source .md/.tex file")
    p.add_argument("--frontier-mode", choices=["openrouter", "gemini-cli"], default="openrouter")
    p.add_argument("--frontier-json", help="Use existing frontier JSON instead of calling remote frontier model")
    p.add_argument("--openrouter-model", default="openrouter/owl-alpha")
    p.add_argument("--leanstral-endpoint", default="http://127.0.0.1:18889/v1")
    p.add_argument("--leanstral-model", default="mistralai_Leanstral-128x3.9B-2603-Q4_K_M.gguf")
    p.add_argument("--timeout", type=int, default=120)
    p.add_argument("--parallel", type=int, default=4, help="Number of parallel refinement workers")
    p.add_argument("--skip-refine", action="store_true", help="Skip local Leanstral chunk-by-chunk refinement")
    p.add_argument("--out-frontier", default="/tmp/semantic_chunks.frontier.json")
    p.add_argument("--out-refined", default="/tmp/semantic_chunks.refined.json")
    p.add_argument("--out-report", default="/tmp/semantic_chunks.report.json")
    return p


if __name__ == "__main__":
    parser = build_parser()
    ns = parser.parse_args()
    try:
        raise SystemExit(run(ns))
    except Exception as exc:  # noqa: BLE001
        print(json.dumps({"status": "FAIL", "error": str(exc)}, ensure_ascii=False))
        raise SystemExit(2)
