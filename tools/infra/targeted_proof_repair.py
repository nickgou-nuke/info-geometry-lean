#!/usr/bin/env python3
"""
Targeted Jung-Pauli-Google recursive proof repair loop.

Target: InfoGeometry.Canonical.ModularCartanCantorSystem.coneVector_mem_naturalCone

Pipeline:
  1. Google AI search for Tomita-Takesaki / natural cone context
  2. Jung generates candidate proof with enriched context
  3. Compile check (lake build the module)
  4. On failure: Pauli/ChatGPT fixes errors from compiler output
  5. Recompile, repeat until green or max iterations
  6. If green: write the proof back to the .lean file

Usage:
    python3 tools/infra/targeted_proof_repair.py \
        --file lean/InfoGeometry/Canonical/ModularCartanCantorSystem.lean \
        --theorem coneVector_mem_naturalCone \
        --max-iterations 5
"""

from __future__ import annotations

import argparse
import json
import logging
import os
import re
import subprocess
import sys
import tempfile
import time
import urllib.request
from pathlib import Path
from typing import Any

_HERE = Path(__file__).resolve().parent
_REPO = _HERE.parents[1]
sys.path.insert(0, str(_REPO))

logger = logging.getLogger("proof_repair")

try:
    from tools.infra.agent_message_ledger import record_message
except Exception:  # pragma: no cover - observation must never block proof repair.
    record_message = None


# ---------------------------------------------------------------------------
# API helper
# ---------------------------------------------------------------------------

def _load_deepseek_key() -> str:
    import configparser
    for key in ["DEEPSEEK_API_KEY", "OPENROUTER_API_KEY"]:
        val = os.environ.get(key, "")
        if val and not val.startswith("***"):
            return val
    env_path = Path.home() / ".hermes" / ".env"
    if env_path.exists():
        config = configparser.ConfigParser()
        try:
            config.read_string("[DEFAULT]\n" + env_path.read_text())
            for k in ["DEEPSEEK_API_KEY", "OPENROUTER_API_KEY", "GOOGLE_API_KEY"]:
                v = config.get("DEFAULT", k, fallback="")
                if v and not v.startswith("***"):
                    return v
        except Exception:
            pass
    return ""


def call_llm(system: str, user: str, model: str = "deepseek-chat",
             temperature: float = 0.2, max_tokens: int = 4096) -> str:
    key = _load_deepseek_key()
    if not key:
        raise RuntimeError("No API key")
    key = key.encode("ascii", errors="ignore").decode("ascii")
    payload = json.dumps({
        "model": model,
        "messages": [
            {"role": "system", "content": system},
            {"role": "user", "content": user},
        ],
        "temperature": temperature,
        "max_tokens": max_tokens,
    }).encode("utf-8")
    req = urllib.request.Request(
        "https://api.deepseek.com/v1/chat/completions",
        data=payload,
        headers={"Content-Type": "application/json", "Authorization": f"Bearer {key}"},
    )
    started = time.monotonic()
    content = ""
    error = ""
    success = False
    try:
        with urllib.request.urlopen(req, timeout=180) as resp:
            data = json.loads(resp.read().decode())
        content = data["choices"][0]["message"]["content"]
        success = True
        return content
    except Exception as exc:
        error = str(exc)
        raise
    finally:
        if record_message is not None:
            try:
                record_message(
                    source_tool="targeted_proof_repair.py",
                    source_file="tools/infra/targeted_proof_repair.py",
                    channel="targeted_proof_repair_llm",
                    provider="deepseek-api",
                    model=model,
                    platform="deepseek",
                    prompt_text=json.dumps(
                        [
                            {"role": "system", "content": system},
                            {"role": "user", "content": user},
                        ],
                        ensure_ascii=False,
                    ),
                    response_text=content or error,
                    success=success,
                    latency_ms=(time.monotonic() - started) * 1000.0,
                    metadata={
                        "temperature": temperature,
                        "max_tokens": max_tokens,
                        "failure_pattern": error,
                    },
                )
            except Exception:
                pass


# ---------------------------------------------------------------------------
# Google AI Search context enrichment
# ---------------------------------------------------------------------------

def google_search_context(query: str) -> str:
    """Try to get Google AI search context. Falls back to static knowledge."""
    try:
        from tools.infra.google_ai_searcher import search_google_ai
        import asyncio
        result = asyncio.run(search_google_ai(query))
        return result.get("summary", "")[:2000]
    except Exception as e:
        logger.warning("Google search failed: %s", e)
        return ""


# ---------------------------------------------------------------------------
# Read the target file and theorem
# ---------------------------------------------------------------------------

def read_target_block(filepath: Path, theorem_name: str) -> dict[str, str]:
    """Read the file and extract: context (everything before the theorem),
    theorem block, and rest (everything after)."""
    text = filepath.read_text(encoding="utf-8")
    lines = text.split("\n")

    # Find the theorem: `theorem theorem_name ...`
    theorem_re = re.compile(
        rf"^(\s*)(@\[[^\]]*\])?\s*theorem\s+{re.escape(theorem_name)}\b"
    )
    start_line = None
    for i, line in enumerate(lines):
        if theorem_re.search(line):
            start_line = i
            break

    if start_line is None:
        raise ValueError(f"Theorem '{theorem_name}' not found in {filepath}")

    # Find the end: next `theorem`, `lemma`, `def`, `end`, `namespace`, or `section`
    end_re = re.compile(
        r"^\s*(?:theorem|lemma|def|structure|inductive|class|end|namespace|section|abbrev)\b"
    )
    end_line = len(lines)
    depth = 0
    for i in range(start_line, len(lines)):
        line = lines[i]
        # Track braces/indentation for nested blocks
        if ":= " in line or ":=" in line:
            # Theorem body starts
            pass
        if end_re.search(line) and i > start_line:
            end_line = i
            break

    context = "\n".join(lines[:start_line])
    theorem_block = "\n".join(lines[start_line:end_line])
    rest = "\n".join(lines[end_line:])

    # Also get imports and the full file header
    imports = []
    for line in lines[:50]:
        if line.strip().startswith("import ") or line.strip().startswith("open "):
            imports.append(line)

    return {
        "imports": "\n".join(imports),
        "context": context,
        "theorem_block": theorem_block,
        "rest": rest,
        "start_line": start_line + 1,
        "end_line": end_line + 1,
    }


# ---------------------------------------------------------------------------
# Compile check
# ---------------------------------------------------------------------------

def compile_check(lean_file: Path) -> dict[str, Any]:
    """Compile a Lean file and return success + errors."""
    start = time.time()
    proc = subprocess.run(
        ["lake", "env", "lean", str(lean_file)],
        cwd=_REPO, capture_output=True, text=True, timeout=120,
    )
    elapsed = time.time() - start
    stdout = proc.stdout[-4000:] if proc.stdout else ""
    stderr = proc.stderr[-4000:] if proc.stderr else ""
    return {
        "success": proc.returncode == 0,
        "stdout": stdout,
        "stderr": stderr,
        "duration_s": elapsed,
    }


def build_module(module_name: str) -> dict[str, Any]:
    """Build a specific module via lake build."""
    start = time.time()
    proc = subprocess.run(
        ["lake", "build", module_name],
        cwd=_REPO, capture_output=True, text=True, timeout=300,
    )
    elapsed = time.time() - start
    return {
        "success": proc.returncode == 0,
        "output": (proc.stdout + "\n" + proc.stderr)[-4000:],
        "duration_s": elapsed,
    }


# ---------------------------------------------------------------------------
# Jung: generate proof (with Google context enrichment)
# ---------------------------------------------------------------------------

JUNG_SYSTEM = """You are a Tomita-Takesaki modular theory expert producing Lean 4 proofs.
You know the mathlib4 API for operator algebras, Hilbert spaces, and modular theory.
Given a theorem target with its file context, produce a complete, compilable Lean 4 proof.

Rules:
- Use ONLY theorems/lemmas already present in mathlib4 or the provided imports
- The theorem name and statement MUST be preserved exactly as given
- Replace `:= by sorry` with a real proof
- Keep the proof self-contained; do not introduce new axioms
- If you cannot produce a full proof, produce the best partial proof with an honest `sorry` marker
"""


def jung_generate(context_block: dict, google_context: str = "",
                  previous_attempt: str = "", compile_error: str = "") -> str:
    """Jung generates a proof attempt."""
    user = f"""## TARGET THEOREM

File: lean/InfoGeometry/Canonical/ModularCartanCantorSystem.lean

{context_block['theorem_block']}

## FILE IMPORTS

{context_block['imports']}

## RELEVANT FILE CONTEXT (abbreviated)

{context_block['context'][-2000:]}"""

    if google_context:
        user += f"""

## GOOGLE AI SEARCH CONTEXT

{google_context[:1500]}"""

    if previous_attempt:
        user += f"""

## PREVIOUS ATTEMPT (FAILED)

Code:
```lean4
{previous_attempt[:2000]}
```

Compiler error:
```
{compile_error[:2000]}
```

Please fix the error and produce a corrected, complete proof."""

    user += """

## INSTRUCTIONS

Output ONLY the lean4 code block with the complete theorem (preserving the exact statement).
Replace `:= by sorry` with a real proof.
Use ```lean4 ... ``` fences."""

    return call_llm(JUNG_SYSTEM, user, max_tokens=4096)


# ---------------------------------------------------------------------------
# Pauli/ChatGPT: fix compilation errors
# ---------------------------------------------------------------------------

PAULI_SYSTEM = """You are a Lean 4 compiler error fixer. Given a Lean theorem that fails to compile
and the exact error messages, produce a corrected version of ONLY the theorem block.

Rules:
- Preserve the theorem name and statement EXACTLY
- Fix only the compilation errors shown
- Do NOT change imports or add new dependencies
- Keep any working parts of the proof unchanged
- Output ONLY the corrected theorem block in ```lean4 ... ``` fences"""


def pauli_fix(theorem_block: str, compile_errors: str, file_imports: str = "") -> str:
    """Pauli fixes compilation errors."""
    user = f"""## THEOREM THAT FAILS TO COMPILE

```lean4
{theorem_block[:3000]}
```

## COMPILER ERRORS

```
{compile_errors[:3000]}
```

## IMPORTS AVAILABLE

{file_imports}

Output the corrected theorem block in ```lean4 ... ``` fences."""

    return call_llm(PAULI_SYSTEM, user, max_tokens=4096)


# ---------------------------------------------------------------------------
# Recursive repair loop
# ---------------------------------------------------------------------------

def extract_lean_code(response: str) -> str:
    """Extract Lean code from LLM response."""
    # Try fenced code block
    m = re.search(r"```(?:lean4|lean)?\s*\n(.*?)```", response, re.DOTALL)
    if m:
        code = m.group(1).strip()
        # Check if it starts with 'theorem' — if not, try to find it
        if not code.strip().startswith("theorem"):
            # Try to find the theorem in the response
            tm = re.search(r"(theorem\s+\w+.*?:=.*?)(?=\n\s*(?:theorem|lemma|def|end|$))",
                          response, re.DOTALL)
            if tm:
                return tm.group(1).strip()
        return code

    # Try without fences
    tm = re.search(r"(theorem\s+\w+.*?:=.*?)(?=\n\s*(?:theorem|lemma|def|end|namespace|$))",
                   response, re.DOTALL)
    if tm:
        return tm.group(1).strip()
    return response.strip()


def repair_loop(
    filepath: Path,
    theorem_name: str,
    max_iterations: int = 5,
    use_google: bool = True,
) -> dict[str, Any]:
    """Main recursive repair loop."""
    logger.info("=== Targeted proof repair: %s / %s ===", filepath.name, theorem_name)

    # Read the target
    block = read_target_block(filepath, theorem_name)
    logger.info("Theorem at lines %d-%d, %d chars",
                block["start_line"], block["end_line"], len(block["theorem_block"]))

    # Google context
    google_ctx = ""
    if use_google:
        logger.info("Google AI search for context...")
        query = "Tomita-Takesaki modular theory standard form natural cone positive functional representation"
        google_ctx = google_search_context(query)
        if google_ctx:
            logger.info("Got Google context: %d chars", len(google_ctx))
        else:
            logger.info("No Google context available (offline/browser not running)")

    # Iterative repair
    current_proof = ""
    compile_error = ""
    history: list[dict] = []

    for iteration in range(1, max_iterations + 1):
        logger.info("--- Iteration %d/%d ---", iteration, max_iterations)

        # Phase 1: Jung generates or regenerates
        if iteration == 1:
            logger.info("Jung: generating initial proof...")
            response = jung_generate(block, google_ctx)
        else:
            logger.info("Jung: regenerating with error feedback...")
            response = jung_generate(block, google_ctx, current_proof, compile_error)

        lean_code = extract_lean_code(response)
        if not lean_code or len(lean_code) < 20:
            logger.warning("Jung produced no usable code (len=%d)", len(lean_code))
            continue

        logger.info("Jung produced %d chars of Lean code", len(lean_code))

        # Phase 2: Compile check the FULL file (not just the block)
        # Write a temporary file with the full context + new proof
        new_file_content = block["context"] + "\n" + lean_code + "\n" + block["rest"]
        with tempfile.NamedTemporaryFile(mode="w", suffix=".lean", delete=False,
                                         dir="/tmp", encoding="utf-8") as f:
            f.write(new_file_content)
            tmp_path = Path(f.name)

        result = compile_check(tmp_path)
        tmp_path.unlink()

        if result["success"]:
            logger.info("COMPILE SUCCESS! Iteration %d", iteration)
            # Write the fix back to the real file
            new_content = block["context"] + "\n" + lean_code + "\n" + block["rest"]
            filepath.write_text(new_content, encoding="utf-8")
            logger.info("Wrote fix to %s", filepath)

            # Verify with lake build
            module_name = str(filepath.relative_to(_REPO)).replace("/", ".").replace(".lean", "")
            logger.info("lake build %s ...", module_name)
            build_result = build_module(module_name)

            return {
                "success": True,
                "iterations": iteration,
                "lean_code": lean_code,
                "build_success": build_result["success"],
                "history": history,
            }

        # Phase 3: Compile failed — extract errors
        compile_error = result["stderr"] or result["stdout"]
        logger.info("Compile FAILED: %d chars of errors", len(compile_error))

        # Show first few errors
        error_lines = [l for l in compile_error.split("\n") if "error:" in l.lower()]
        for el in error_lines[:3]:
            logger.info("  %s", el.strip()[:150])

        # Phase 4: Pauli fixes
        logger.info("Pauli: fixing compilation errors...")
        fix_response = pauli_fix(lean_code, compile_error, block["imports"])
        fixed_code = extract_lean_code(fix_response)

        if fixed_code and len(fixed_code) > 20:
            current_proof = fixed_code
            logger.info("Pauli produced %d chars fix", len(fixed_code))
        else:
            current_proof = lean_code
            logger.warning("Pauli fix empty, retrying Jung with errors")

        history.append({
            "iteration": iteration,
            "jung_chars": len(lean_code),
            "pauli_chars": len(fixed_code) if fixed_code else 0,
            "compile_success": False,
            "errors_truncated": compile_error[:500],
        })

    return {
        "success": False,
        "iterations": max_iterations,
        "last_error": compile_error[:2000],
        "history": history,
    }


# ---------------------------------------------------------------------------
# CLI
# ---------------------------------------------------------------------------

def main():
    parser = argparse.ArgumentParser(description="Targeted proof repair loop")
    parser.add_argument("--file", required=True, help="Path to .lean file")
    parser.add_argument("--theorem", required=True, help="Theorem name to repair")
    parser.add_argument("--max-iterations", type=int, default=5)
    parser.add_argument("--no-google", action="store_true", help="Skip Google search")
    parser.add_argument("--verbose", action="store_true")
    args = parser.parse_args()

    logging.basicConfig(
        level=logging.DEBUG if args.verbose else logging.INFO,
        format="%(asctime)s %(levelname)s [%(name)s] %(message)s",
    )

    filepath = _REPO / args.file if not args.file.startswith("/") else Path(args.file)
    if not filepath.exists():
        logger.error("File not found: %s", filepath)
        sys.exit(1)

    result = repair_loop(
        filepath=filepath,
        theorem_name=args.theorem,
        max_iterations=args.max_iterations,
        use_google=not args.no_google,
    )

    if result["success"]:
        logger.info("SUCCESS: %s.%s repaired in %d iterations",
                    filepath.stem, args.theorem, result["iterations"])
        if result.get("build_success"):
            logger.info("lake build: PASS")
        else:
            logger.info("lake build: FAIL (file compiles but module build may have dependency issues)")
    else:
        logger.info("FAILED after %d iterations", result["iterations"])
        if result.get("last_error"):
            logger.info("Last error:\n%s", result["last_error"][:1000])


if __name__ == "__main__":
    main()
