#!/usr/bin/env python3
"""Losslessly render AI Studio exports and index their fenced source blocks.

This is an intake tool only: extracted Lean snippets are candidates and are not
compiled, merged, or promoted into repository owner files by this script.
"""

from __future__ import annotations

import argparse
import hashlib
import json
import re
from collections import Counter
from pathlib import Path
from typing import Any


LEAN_LANGS = {"lean", "lean4"}
LEAN_MARKERS = re.compile(
    r"(?m)^\s*(?:import\s+Mathlib|import\s+|namespace\s+|theorem\s+|lemma\s+|def\s+|abbrev\s+|structure\s+|inductive\s+|class\s+|example\s+|variable\s+|by\s*$)"
)


def normalize_turns(data: Any) -> list[dict[str, Any]]:
    """Accept native Drive JSON, the 1YHH browser extraction, or turn lists."""
    if isinstance(data, dict):
        prompt = data.get("chunkedPrompt")
        if isinstance(prompt, dict) and isinstance(prompt.get("chunks"), list):
            return list(prompt["chunks"])
        if data and all(isinstance(v, dict) and "text" in v for v in data.values()):
            return [dict(v, _turnId=k) for k, v in data.items()]
    if isinstance(data, list):
        if all(isinstance(v, dict) for v in data):
            return data
    raise ValueError("unrecognized AI Studio export schema")


def sha256(data: bytes) -> str:
    return hashlib.sha256(data).hexdigest()


def extract_fences(text: str) -> list[tuple[str, str, bool]]:
    """Extract Markdown fences, preserving even blocks with a missing closer."""
    result: list[tuple[str, str, bool]] = []
    opening: str | None = None
    body: list[str] = []
    for line in text.splitlines(keepends=True):
        if opening is None:
            if line.startswith("```"):
                opening = line[3:].strip().lower()
                body = []
            continue
        if line.startswith("```") and not line[3:].strip():
            result.append((opening, "".join(body), True))
            opening = None
            body = []
        else:
            body.append(line)
    if opening is not None:
        result.append((opening, "".join(body), False))
    return result


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("inputs", nargs="+", type=Path)
    parser.add_argument("--output-dir", type=Path, required=True)
    args = parser.parse_args()
    args.output_dir.mkdir(parents=True, exist_ok=True)

    for source in args.inputs:
        raw = source.read_bytes()
        data = json.loads(raw)
        turns = normalize_turns(data)
        stem = source.name.removesuffix(".json")
        out = args.output_dir / stem
        out.mkdir(parents=True, exist_ok=True)

        transcript: list[str] = [
            f"# AI Studio transcript: `{source.name}`", "",
            f"Source path: `{source}`",
            f"Source bytes: {len(raw)}",
            f"Source SHA-256: `{sha256(raw)}`", "",
        ]
        lean_blocks: list[str] = [f"# Tagged Lean code blocks: `{source.name}`", ""]
        candidate_blocks: list[str] = [
            f"# Unlabelled Lean-like code blocks (unverified candidates): `{source.name}`", ""
        ]
        math_blocks: list[str] = [f"# Extracted inline/display math regions: `{source.name}`", ""]
        all_fences_path = out / "all_code_fences.jsonl"
        all_fences_file = all_fences_path.open("w", encoding="utf-8")
        role_counts: Counter[str] = Counter()
        language_counts: Counter[str] = Counter()
        fence_count = lean_count = candidate_count = 0
        math_count = 0
        timestamps: list[str] = []
        total_chars = 0

        for i, turn in enumerate(turns, 1):
            role = str(turn.get("role", "unknown"))
            stamp = turn.get("createTime") or turn.get("timestamp") or turn.get("time")
            body = str(turn.get("text", "") or "")
            role_counts[role] += 1
            total_chars += len(body)
            if stamp:
                timestamps.append(str(stamp))
            # The raw source JSON remains lossless; rstrip here only avoids
            # introducing trailing-whitespace lint noise in the Markdown view.
            rendered_body = "\n".join(line.rstrip() for line in body.splitlines())
            transcript.extend([f"## Turn {i:04d} — {role}" + (f" — {stamp}" if stamp else ""), "", rendered_body, ""])

            for j, (language, code, closed) in enumerate(extract_fences(body), 1):
                fence_count += 1
                language_counts[language or "(unlabelled)"] += 1
                all_fences_file.write(json.dumps({
                    "turn": i, "role": role, "timestamp": stamp,
                    "fence": j, "language": language, "closed": closed, "code": code,
                }, ensure_ascii=False) + "\n")
                close_note = "" if closed else " — UNTERMINATED IN SOURCE"
                header = f"## Turn {i:04d}, fence {j:03d} — {role}; language `{language or '(unlabelled)'}`{close_note}"
                rendered_code = "\n".join(line.rstrip() for line in code.splitlines())
                if language in LEAN_LANGS:
                    lean_count += 1
                    lean_blocks.extend([header, "", f"```{language}", rendered_code, "```", ""])
                elif not language and LEAN_MARKERS.search(code):
                    candidate_count += 1
                    candidate_blocks.extend([header, "", "```text", rendered_code, "```", ""])
            # Drive JSON stores LaTeX directly in text, unlike DOM exports
            # whose rendered expressions may be supplied separately in pres.
            expressions = turn.get("pres", []) or re.findall(
                r"(?<!\\)\$\$[\s\S]*?(?<!\\)\$\$|"
                r"\\\[[\s\S]*?\\\]|\\\([\s\S]*?\\\)|"
                r"(?<![\\$])\$(?!\$)(?:\\.|[^$\\])*?(?<!\\)\$(?!\$)",
                re.sub(r"(?ms)^```[^\n]*\n.*?^```[^\n]*", "", body),
            )
            for j, expression in enumerate(expressions, 1):
                math_count += 1
                rendered_expression = "\n".join(
                    line.rstrip() for line in str(expression).splitlines()
                )
                math_blocks.extend([f"## Turn {i:04d}, expression {j:03d} — {role}", "", rendered_expression, ""])

        all_fences_file.close()

        (out / "transcript.md").write_text("\n".join(transcript).rstrip() + "\n", encoding="utf-8")
        (out / "lean_fences.md").write_text("\n".join(lean_blocks).rstrip() + "\n", encoding="utf-8")
        (out / "unlabelled_lean_candidates.md").write_text(
            "\n".join(candidate_blocks).rstrip() + "\n", encoding="utf-8"
        )
        (out / "math_expressions.md").write_text("\n".join(math_blocks).rstrip() + "\n", encoding="utf-8")
        manifest = {
            "math_expression_count": math_count,
            "source_name": source.name,
            "source_path": str(source),
            "source_bytes": len(raw),
            "source_sha256": sha256(raw),
            "turn_count": len(turns),
            "role_counts": dict(role_counts),
            "transcript_characters": total_chars,
            "fence_count": fence_count,
            "fence_languages": dict(language_counts),
            "tagged_lean_fences": lean_count,
            "unterminated_fences": sum(
                not closed for turn in turns for _, _, closed in extract_fences(str(turn.get("text", "") or ""))
            ),
            "unlabelled_lean_candidates": candidate_count,
            "first_timestamp": timestamps[0] if timestamps else None,
            "last_timestamp": timestamps[-1] if timestamps else None,
            "authority": "transcript extraction only; no theorem or proof is promoted",
        }
        (out / "manifest.json").write_text(
            json.dumps(manifest, ensure_ascii=False, indent=2) + "\n", encoding="utf-8"
        )
        print(json.dumps(manifest, ensure_ascii=False))
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
