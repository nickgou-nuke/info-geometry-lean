#!/usr/bin/env python3
"""
LLM Oracle search for lemma proofs, error fixing, and semantic concept lookup.

Reimplements and generalises the oracle scripts from the auto/ codebase
(ask_oracle_lemmas.py, fix_lean_with_oracle.py) as a unified tool with:

- ``--ask``      : generate lemmas for a mathematical statement
- ``--fix``      : repair a broken Lean file using compiler errors
- ``--search``   : semantic concept search across the codebase + mathlib
- ``--translate``: translate a SymPy/Isabelle proof into Lean 4

Supports DeepSeek (default), OpenAI, and generic OpenAI-compatible endpoints.

Usage:
  # Generate lemmas
  python3 tools/leantrail/oracle_search.py --ask                              \
    "Prove that for the boundary matrices of a TwoComplex, rank(d1) + rank(d2) = rank(laplacian1)"

  # Fix a broken file
  python3 tools/leantrail/oracle_search.py --fix lean/DAG/GaussianElimination.lean

  # Semantic search
  python3 tools/leantrail/oracle_search.py --search "discrete Hodge theorem Eckmann"

  # Translate Isabelle/SymPy to Lean
  python3 tools/leantrail/oracle_search.py --translate                          \
    --from isabelle /tmp/dl_rank.thy
"""

from __future__ import annotations

import argparse
import json
import os
import re
import subprocess
import sys
import urllib.request
from pathlib import Path
from typing import Any, Dict, List, Optional, Tuple

# ---------------------------------------------------------------------------
# Configuration
# ---------------------------------------------------------------------------

REPO_ROOT = Path(__file__).resolve().parents[2]
API_KEY_ENV = "DEEPSEEK_API_KEY"
API_KEY_FILE = ".DEEPSEEK_API_KEY"

DEFAULT_MODEL = "deepseek-chat"
DEFAULT_ENDPOINT = "https://api.deepseek.com/v1/chat/completions"
DEFAULT_MAX_TOKENS = 8192
DEFAULT_TEMPERATURE = 0.1

SYSTEM_PROMPT = (
    "You are a Lean 4 expert and mathematical proof assistant. "
    "Write only compilable Lean 4 code using mathlib4. "
    "Use `import Mathlib` or specific imports. "
    "For noncommutative algebra, use `noncomm_ring`. "
    "For rational arithmetic, use `ring`, `field_simp`, `nlinarith`. "
    "For matrix/linear algebra, use `Matrix.rank`, `finrank`, `LinearMap`. "
    "Never use `sorry` or `admit`."
)


# ---------------------------------------------------------------------------
# API helpers
# ---------------------------------------------------------------------------


def _load_api_key() -> str:
    """Load API key from environment or file."""
    key = os.environ.get(API_KEY_ENV)
    if key:
        return key

    candidates = [
        REPO_ROOT / API_KEY_FILE,
        Path.home() / API_KEY_FILE,
    ]
    for path in candidates:
        if not path.exists():
            continue
        try:
            content = path.read_text(encoding="utf-8").strip()
            for line in content.splitlines():
                if line.startswith("export"):
                    key = line.split("=", 1)[1].strip().strip('"').strip("'")
                    if key:
                        return key
                elif len(line) > 20 and not line.startswith("#"):
                    return line.strip()
        except Exception:
            continue

    raise SystemExit(
        f"No API key found. Set {API_KEY_ENV} or create {API_KEY_FILE} in repo root."
    )


def _call_llm(
    prompt: str,
    *,
    model: str = DEFAULT_MODEL,
    endpoint: str = DEFAULT_ENDPOINT,
    max_tokens: int = DEFAULT_MAX_TOKENS,
    temperature: float = DEFAULT_TEMPERATURE,
    system: str = SYSTEM_PROMPT,
) -> str:
    """Call an OpenAI-compatible chat completion endpoint."""
    api_key = _load_api_key()

    data = json.dumps({
        "model": model,
        "messages": [
            {"role": "system", "content": system},
            {"role": "user", "content": prompt},
        ],
        "max_tokens": max_tokens,
        "temperature": temperature,
    }).encode()

    req = urllib.request.Request(
        endpoint,
        data=data,
        headers={
            "Content-Type": "application/json",
            "Authorization": f"Bearer {api_key}",
        },
    )

    print(f"  Calling {model} ({endpoint}) ...", file=sys.stderr)
    resp = urllib.request.urlopen(req, timeout=120)
    result = json.loads(resp.read())
    return result["choices"][0]["message"]["content"]


def _extract_lean_code(text: str) -> str:
    """Extract Lean code block from LLM response."""
    for marker in ("```lean4", "```lean", "```"):
        if marker in text:
            parts = text.split(marker, 1)[1].split("```", 1)
            return parts[0].strip()
    return text.strip()


# ---------------------------------------------------------------------------
# Lean compiler
# ---------------------------------------------------------------------------


def _run_lean(filepath: Path, timeout: int = 45) -> Tuple[int, str, str]:
    """Compile a Lean file, returning (exit_code, stdout, stderr)."""
    result = subprocess.run(
        ["timeout", str(timeout), "lake", "env", "lean", str(filepath.resolve())],
        capture_output=True,
        text=True,
        cwd=str(REPO_ROOT),
    )
    return result.returncode, result.stdout, result.stderr


# ---------------------------------------------------------------------------
# Local semantic search helpers
# ---------------------------------------------------------------------------


def _query_tokens(query: str) -> List[str]:
    """Tokenise a semantic query into useful search atoms."""
    raw = re.findall(r"[A-Za-z_][A-Za-z0-9_']*", query)
    stop = {
        "the", "and", "for", "with", "from", "into", "that", "this", "prove",
        "lemma", "theorem", "lean", "mathlib", "search", "find", "about",
    }
    return [t for t in raw if len(t) > 2 and t.lower() not in stop]


def _candidate_search_roots() -> List[Path]:
    """Repo/mathlib roots for local proof-source search."""
    roots = [REPO_ROOT / "lean"]
    mathlib = REPO_ROOT / ".lake" / "packages" / "mathlib" / "Mathlib"
    if mathlib.exists():
        roots.append(mathlib)
    return [p for p in roots if p.exists()]


def _local_semantic_search(query: str, limit: int = 20) -> List[Dict[str, Any]]:
    """Lightweight local declaration/line search across repo Lean files and mathlib.

    This deliberately runs before any remote oracle call so the oracle is grounded
    in actual repository/mathlib text rather than guessing lemma names.
    """
    tokens = _query_tokens(query)
    if not tokens:
        tokens = [query]
    lowered = [t.lower() for t in tokens]
    exact = query.lower().strip()

    hits: List[Dict[str, Any]] = []
    decl_re = re.compile(
        r"^\s*(?:@[\w\[\], .]+\s*)*(?:noncomputable\s+)?"
        r"(theorem|lemma|def|abbrev|structure|class|inductive|instance)\s+"
        r"([A-Za-z_][A-Za-z0-9_']*)"
    )

    for root in _candidate_search_roots():
        for path in root.rglob("*.lean"):
            if any(part in {".lake", ".git", "lean_sandbox", "external_refs"} for part in path.parts):
                continue
            try:
                lines = path.read_text(encoding="utf-8", errors="ignore").splitlines()
            except OSError:
                continue
            current_decl: Optional[str] = None
            current_kind: Optional[str] = None
            for lineno, line in enumerate(lines, start=1):
                m = decl_re.match(line)
                if m:
                    current_kind, current_decl = m.group(1), m.group(2)
                low = line.lower()
                score = 0
                if exact and exact in low:
                    score += 10
                score += sum(1 for t in lowered if t in low)
                if current_decl:
                    decl_low = current_decl.lower()
                    score += sum(2 for t in lowered if t in decl_low)
                if score > 0:
                    rel = path.relative_to(REPO_ROOT) if path.is_relative_to(REPO_ROOT) else path
                    hits.append({
                        "score": score,
                        "file": str(rel),
                        "line": lineno,
                        "kind": current_kind,
                        "decl": current_decl,
                        "text": line.strip()[:240],
                    })

    hits.sort(key=lambda h: (-int(h["score"]), str(h["file"]), int(h["line"])))
    deduped: List[Dict[str, Any]] = []
    seen: Set[Tuple[str, int]] = set()
    for h in hits:
        key = (str(h["file"]), int(h["line"]))
        if key in seen:
            continue
        seen.add(key)
        deduped.append(h)
        if len(deduped) >= limit:
            break
    return deduped


def _format_local_hits(hits: List[Dict[str, Any]]) -> str:
    if not hits:
        return "No local Lean/mathlib hits found."
    lines = []
    for h in hits:
        decl = f" {h['kind']} {h['decl']}" if h.get("decl") else ""
        lines.append(f"- {h['file']}:{h['line']}:{decl} :: {h['text']}")
    return "\n".join(lines)


# ---------------------------------------------------------------------------
# Commands
# ---------------------------------------------------------------------------


def cmd_ask(args: argparse.Namespace) -> int:
    """Generate lemmas for a mathematical statement."""
    prompt = f"""Write a series of Lean 4 lemmas proving: {args.ask}

Use only `import Mathlib` and standard mathlib4 imports.
Write complete proofs using the canonical mathlib4 style.
Include type annotations. Use `calc`, `ring`, `field_simp`, `nlinarith` where appropriate.
For matrix rank, use `Matrix.rank` and `LinearMap.finrank_range_add_finrank_ker`.
Format each lemma as a separate `lemma` block with docstring."""
    if args.extra:
        prompt += f"\n\nAdditional requirements: {args.extra}"

    response = _call_llm(prompt, model=args.model, endpoint=args.endpoint)
    code = _extract_lean_code(response)

    out_path = Path(args.out or "/tmp/oracle_lemmas.lean").resolve()
    out_path.parent.mkdir(parents=True, exist_ok=True)
    out_path.write_text(code, encoding="utf-8")

    n_lemmas = code.count("lemma ") + code.count("theorem ")
    print(f"  Generated: {n_lemmas} lemmas, {len(code)} chars -> {out_path}")

    if args.compile:
        print("  Compiling ...")
        rc, stdout, stderr = _run_lean(out_path)
        if rc == 0:
            print("  COMPILATION SUCCESS")
        else:
            print(f"  Compilation failed (rc={rc}):")
            print(stderr[-600:])
    return 0


def cmd_fix(args: argparse.Namespace) -> int:
    """Repair a broken Lean file."""
    filepath = Path(args.fix).resolve()
    if not filepath.exists():
        print(f"Error: file not found: {filepath}", file=sys.stderr)
        return 1

    code = filepath.read_text(encoding="utf-8")

    # Get compiler errors
    print(f"  Compiling {filepath} ...")
    rc, stdout, stderr = _run_lean(filepath)
    if rc == 0:
        print("  File already compiles! No fixes needed.")
        return 0

    errors = stderr[-3000:] if stderr else "No errors captured"

    prompt = f"""You are a Lean 4 expert. Fix ALL compilation errors in this file.
Return the COMPLETE corrected file as a single `lean4` code block.

ERRORS:
```
{errors}
```

FILE TO FIX:
```lean4
{code}
```

Requirements:
1. Fix ALL compilation errors
2. Keep the same theorem/lemma names and structure
3. Use only standard mathlib4 lemmas and tactics
4. Never use `sorry` or `admit`
5. Return ONLY the complete corrected code, no explanation
"""

    response = _call_llm(prompt, model=args.model, endpoint=args.endpoint)
    fixed = _extract_lean_code(response)

    if args.in_place:
        filepath.write_text(fixed, encoding="utf-8")
        print(f"  Wrote {len(fixed)} chars to {filepath}")
    else:
        out_path = Path(args.out or str(filepath.with_suffix(".fixed.lean"))).resolve()
        out_path.write_text(fixed, encoding="utf-8")
        print(f"  Wrote {len(fixed)} chars to {out_path}")

    if args.compile:
        verify_path = filepath if args.in_place else out_path
        print("  Verifying compilation ...")
        rc, stdout, stderr = _run_lean(verify_path)
        if rc == 0:
            print("  COMPILATION SUCCESS!")
        else:
            print(f"  Still broken (rc={rc}). May need iterative fixing.")
            print(stderr[-500:])
    return 0


def cmd_search(args: argparse.Namespace) -> int:
    """Semantic search grounded by local repo/mathlib hits, optionally followed by LLM synthesis."""
    local_hits = _local_semantic_search(args.search, limit=args.limit)
    local_text = _format_local_hits(local_hits)

    print("LOCAL REPO/MATHLIB HITS:")
    print(local_text)

    if args.local_only:
        if args.out:
            Path(args.out).write_text(local_text + "\n", encoding="utf-8")
        return 0

    prompt = f"""Search mathlib4 and the Lean mathematical literature for:
{args.search}

First use these actual local repository/mathlib hits as grounding evidence:
{local_text}

Return:
1. Relevant local declarations, with file paths, if they match the query
2. Relevant mathlib4 lemma names with their type signatures when known
3. A proof-source plan explaining which local/mathlib lemmas to inspect first

Format each finding as:
- `LemmaName` : type_signature_or_file_location  -- brief description

Do not claim a lemma is absent if it appears in the local hits.  Do not invent
proof closure; this is search guidance only.  For linear algebra, use
`Matrix.rank`, `finrank`, `LinearMap` lemmas. For combinatorics, use `Finset`,
`Finsupp`. For noncommutative algebra, use `TensorAlgebra`, `RingQuot`."""
    if args.extra:
        prompt += f"\n\nAdditional context: {args.extra}"

    response = _call_llm(prompt, model=args.model, endpoint=args.endpoint)
    combined = "LOCAL REPO/MATHLIB HITS:\n" + local_text + "\n\nORACLE SYNTHESIS:\n" + response
    print("\nORACLE SYNTHESIS:")
    print(response)

    if args.out:
        Path(args.out).write_text(combined, encoding="utf-8")
    return 0


def cmd_translate(args: argparse.Namespace) -> int:
    """Translate a proof from SymPy/Isabelle/Python into Lean 4."""
    source_path = Path(args.translate).resolve()
    if not source_path.exists():
        print(f"Error: source file not found: {source_path}", file=sys.stderr)
        return 1

    source_code = source_path.read_text(encoding="utf-8")
    source_lang = args.from_lang or source_path.suffix.lstrip(".")

    prompt = f"""Translate the following {source_lang} proof into Lean 4 using mathlib4.

{source_lang.upper()} SOURCE:
```{source_lang}
{source_code}
```

Requirements:
1. Write complete, compilable Lean 4 code
2. Use mathlib4 canonical patterns and lemma names
3. Preserve the mathematical content exactly
4. Include all necessary imports
5. Return ONLY the Lean 4 code block
"""
    if args.extra:
        prompt += f"\nAdditional context: {args.extra}"

    response = _call_llm(prompt, model=args.model, endpoint=args.endpoint)
    code = _extract_lean_code(response)

    out_path = Path(args.out or str(source_path.with_suffix(".lean"))).resolve()
    out_path.write_text(code, encoding="utf-8")
    print(f"  Translated {len(source_code)} chars -> {len(code)} chars Lean")
    print(f"  Output: {out_path}")

    if args.compile:
        print("  Compiling ...")
        rc, stdout, stderr = _run_lean(out_path)
        if rc == 0:
            print("  COMPILATION SUCCESS")
        else:
            print(f"  Compilation failed (rc={rc}):")
            print(stderr[-600:])
    return 0


# ---------------------------------------------------------------------------
# CLI
# ---------------------------------------------------------------------------


def _parse_args() -> argparse.Namespace:
    parser = argparse.ArgumentParser(
        description="LLM Oracle: lemma generation, error fixing, semantic search, translation."
    )
    parser.add_argument("--model", default=DEFAULT_MODEL)
    parser.add_argument("--endpoint", default=DEFAULT_ENDPOINT)
    parser.add_argument("--out", default=None, help="Output file path")
    parser.add_argument("--extra", default=None, help="Extra prompt context")
    parser.add_argument("--compile", action="store_true",
                        help="Attempt to compile the output with Lean")
    parser.add_argument("--limit", type=int, default=20,
                        help="Maximum local search hits for --search (default: 20)")
    parser.add_argument("--local-only", action="store_true",
                        help="For --search, return local repo/mathlib hits without an LLM call")

    sub = parser.add_mutually_exclusive_group(required=True)
    sub.add_argument("--ask", type=str, default=None,
                     help="Mathematical statement to generate lemmas for")
    sub.add_argument("--fix", type=str, default=None,
                     help="Path to a broken Lean file to fix")
    sub.add_argument("--search", type=str, default=None,
                     help="Semantic concept/lemma search query")
    sub.add_argument("--translate", type=str, default=None,
                     help="Path to a SymPy/Isabelle/Python proof to translate")

    parser.add_argument("--in-place", action="store_true",
                        help="Overwrite the input file with the fixed version")
    parser.add_argument("--from-lang", dest="from_lang", default=None,
                        help="Source language for translation (py, thy, sage)")
    return parser.parse_args()


def main() -> int:
    args = _parse_args()

    if args.ask:
        return cmd_ask(args)
    if args.fix:
        return cmd_fix(args)
    if args.search:
        return cmd_search(args)
    if args.translate:
        return cmd_translate(args)

    print("No command specified. Use --ask, --fix, --search, or --translate.",
          file=sys.stderr)
    return 1


if __name__ == "__main__":
    raise SystemExit(main())
