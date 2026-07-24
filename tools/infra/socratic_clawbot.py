#!/usr/bin/env python3
"""Socratic Lean proof repair prompt via browser-harness + ChatGPT.

This replaces the aiClaw adapter with a browser-harness driver that works with
ChatGPT (and Google AI Search via the same harness). It preserves the Hermes
lesson: send the complete owner file plus all relevant Lean errors in one prompt.
No automatic overwrite of Lean source.
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
from pathlib import Path
from typing import Any

if __package__ in (None, ""):
    sys.path.insert(0, str(Path(__file__).resolve().parents[2]))

from tools.infra.lean_audit_prompt import extract_replacement_lean, lean_candidate_reject_reason


ROOT = Path(__file__).resolve().parents[2]
PROMPT_PROFILE_DIR = ROOT / "configs" / "oracle_prompt_profiles"
logger = logging.getLogger("socratic_clawbot")

# Browser-harness configuration
CHATGPT_URL = os.environ.get("CHATGPT_URL", "https://chatgpt.com/?temporary-chat=true")
CHATGPT_RESULT_JSON = Path(os.environ.get("CHATGPT_RESULT_JSON", "/tmp/socratic_browser_result.json"))
CHATGPT_TIMEOUT_SECONDS = int(os.environ.get("CHATGPT_TIMEOUT_SECONDS", "600"))
CHATGPT_POLL_SECONDS = float(os.environ.get("CHATGPT_POLL_SECONDS", "5"))


def read_theorem_block(filepath: Path, theorem_name: str) -> dict[str, Any]:
    text = filepath.read_text(encoding="utf-8")
    lines = text.splitlines()
    theorem_re = re.compile(rf"^\s*(@\[[^\]]*\])?\s*(theorem|lemma)\s+{re.escape(theorem_name)}\b")
    start_line = None
    for index, line in enumerate(lines):
        if theorem_re.search(line):
            start_line = index
            break
    if start_line is None:
        raise ValueError(f"Theorem or lemma {theorem_name!r} not found in {filepath}")

    end_re = re.compile(r"^\s*(?:theorem|lemma|def|structure|inductive|class|end|namespace|section|abbrev)\b")
    end_line = len(lines)
    for index in range(start_line + 1, len(lines)):
        if end_re.search(lines[index]):
            end_line = index
            break

    return {
        "theorem_block": "\n".join(lines[start_line:end_line]),
        "file_context": text,
        "start_line": start_line + 1,
        "end_line": end_line,
    }


def compile_check(lean_file: Path, timeout: int) -> dict[str, Any]:
    try:
        proc = subprocess.run(
            ["lake", "env", "lean", str(lean_file)],
            cwd=ROOT,
            capture_output=True,
            text=True,
            timeout=timeout,
            check=False,
        )
        return {
            "cmd": ["lake", "env", "lean", str(lean_file)],
            "returncode": proc.returncode,
            "stdout": proc.stdout,
            "stderr": proc.stderr,
            "success": proc.returncode == 0,
        }
    except subprocess.TimeoutExpired as exc:
        return {
            "cmd": ["lake", "env", "lean", str(lean_file)],
            "returncode": None,
            "stdout": exc.stdout or "",
            "stderr": exc.stderr or "",
            "success": False,
            "timeout": True,
        }


def available_prompt_profiles() -> list[str]:
    if not PROMPT_PROFILE_DIR.exists():
        return []
    return sorted(path.stem for path in PROMPT_PROFILE_DIR.glob("*.md") if path.is_file())


def load_prompt_profile(name: str | None) -> tuple[str, str]:
    if not name:
        return "builtin", ""
    if not re.match(r"^[A-Za-z0-9_.-]+$", name):
        raise ValueError(f"invalid prompt profile name: {name!r}")
    path = PROMPT_PROFILE_DIR / f"{name}.md"
    if not path.exists():
        profiles = ", ".join(available_prompt_profiles()) or "(none)"
        raise FileNotFoundError(f"prompt profile {name!r} not found in {PROMPT_PROFILE_DIR}; available: {profiles}")
    return name, path.read_text(encoding="utf-8").strip()


def load_prompt_addendum(profile: str | None, prompt_file: str | None) -> tuple[str, str]:
    profile_name, profile_text = load_prompt_profile(profile)
    file_text = ""
    if prompt_file:
        path = Path(prompt_file)
        if not path.is_absolute():
            path = ROOT / path
        file_text = path.read_text(encoding="utf-8").strip()
        if profile_name == "builtin":
            profile_name = path.stem

    addendum = "\n\n".join(part for part in [profile_text, file_text] if part)
    return profile_name, addendum


def build_oracle_prompt(
    *,
    filepath: Path,
    theorem_name: str,
    theorem_block: str,
    file_context: str,
    lean_check: dict[str, Any],
    system_addendum: str = "",
) -> str:
    build_output = "\n".join(
        part for part in [lean_check.get("stderr", ""), lean_check.get("stdout", "")] if part
    ).strip()
    if not build_output and lean_check.get("success"):
        build_output = "Current owner file checks successfully. Audit the target proof for robustness and minimality."

    addendum_block = ""
    if system_addendum.strip():
        addendum_block = f"""
Additional oracle system discipline:

```text
{system_addendum.strip()}
```
"""

    return f"""Review this Lean 4 proof repair as a concrete owner-file task.
Repo: info-geometry-lean.
Owner file: {filepath}
Target theorem: {theorem_name}
Target starts at line: {theorem_block.splitlines()[0] if theorem_block else theorem_name}
{addendum_block}

The complete owner file is below.

```lean4
{file_context}
```

The complete relevant Lean build output is below.

```text
{build_output}
```

Return only:
1. the actual cause of the failure or fragility,
2. the complete corrected Lean owner file,
3. any mathlib API semantic correction.

Canonical response format, exactly:

### Cause
One concise paragraph.

### Replacement
```lean4
-- Return the complete corrected content of the Lean owner file.
-- This is file-in/file-out replacement: the whole broken .lean file is replaced
-- by this whole corrected .lean file.
-- Use ordinary Lean line breaks and indentation. Do not minify into one line.
-- Do not use escaped "\\n" text. If no change is needed, put only:
-- no replacement needed
```

### API
One concise paragraph, or "No API correction."

Do not propose a broad rewrite. Keep the file small, cohesive, and mathlib-style:
one owner purpose, minimal imports, local helper lemmas only when they reduce
the proof. Do not hide the proof in wrappers, certificates, axioms, fake
instances, or vacuous True theorems. If the file already checks, focus on
whether the proof can be simplified without changing theorem content.
"""


def extract_lean_code(text: str) -> str:
    if not text:
        return ""
    replacement = extract_replacement_lean(text)
    if replacement:
        return replacement
    match = re.search(r"```(?:lean4|lean)?\s*\n?(.*?)```", text, re.DOTALL)
    if match:
        return normalize_lean_code(match.group(1))
    match = re.search(r"^\s*(?:theorem|lemma)\b", text, re.MULTILINE)
    return normalize_lean_code(text[match.start():]) if match else ""


def response_readback_reason(text: str, candidate: str) -> str:
    """Return a reason when the transport payload violates the repair contract."""
    if not text.strip():
        return ""
    no_replacement = re.search(r"\bno replacement needed\b", text, re.IGNORECASE)
    replacement_seen = re.search(r"(?im)^\s*(?:###\s*)?Replacement\s*$", text)
    has_code_fence = "```" in text
    if replacement_seen and not has_code_fence and not no_replacement:
        return "replacement_section_missing_code_fence"
    flattened_lean_marker = re.search(
        r"\b(?:lean4|lean)(?:import|open|namespace|section|noncomputable|def|theorem|lemma)\b",
        text,
    )
    if flattened_lean_marker:
        return "flattened_lean_code_block"
    if candidate and "\n" not in candidate and len(candidate) > 300:
        return "single_line_large_candidate"
    if candidate:
        reject_reason = lean_candidate_reject_reason(candidate)
        if reject_reason:
            return reject_reason
    if not candidate and not no_replacement:
        reject_reason = lean_candidate_reject_reason(text, allow_snippet=True)
        if reject_reason == "natural_language_candidate":
            return reject_reason
    return ""


def normalize_lean_code(code: str) -> str:
    stripped = code.strip()
    if "\n" not in stripped and "\\n" in stripped:
        stripped = stripped.replace("\\r\\n", "\n").replace("\\n", "\n").replace("\\t", "  ")
    return stripped


def write_json(path: Path, payload: dict[str, Any]) -> None:
    path.parent.mkdir(parents=True, exist_ok=True)
    path.write_text(json.dumps(payload, indent=2, sort_keys=True) + "\n", encoding="utf-8")


def run_browser_harness(prompt: str, timeout: int = CHATGPT_TIMEOUT_SECONDS) -> dict[str, Any]:
    """Execute the browser-harness driver with the given prompt."""
    with tempfile.NamedTemporaryFile(mode="w", suffix=".txt", delete=False) as f:
        f.write(prompt)
        prompt_file = f.name

    try:
        env = os.environ.copy()
        env["CHATGPT_PROMPT_FILE"] = prompt_file
        env["BU_CDP_WS"] = os.environ.get("BU_CDP_WS", "")
        env["CHATGPT_URL"] = CHATGPT_URL
        env["CHATGPT_RESULT_JSON"] = str(CHATGPT_RESULT_JSON)
        env["CHATGPT_TIMEOUT_SECONDS"] = str(timeout)
        env["CHATGPT_POLL_SECONDS"] = str(CHATGPT_POLL_SECONDS)

        harness_script = f'''import sys
sys.path.insert(0, "{ROOT}")
exec(open("tools/infra/chatgpt_browser_harness_driver.py").read())
_main()
'''

        result = subprocess.run(
            ["browser-harness"],
            input=harness_script,
            cwd=ROOT,
            env=env,
            capture_output=True,
            text=True,
            timeout=timeout,
        )

        if CHATGPT_RESULT_JSON.exists():
            content = CHATGPT_RESULT_JSON.read_text()
            try:
                return json.loads(content)
            except json.JSONDecodeError:
                return {"content": content, "success": True, "dry_run": False}

        return {
            "content": result.stdout,
            "success": result.returncode == 0,
            "dry_run": False,
            "stderr": result.stderr,
        }

    except subprocess.TimeoutExpired:
        return {"content": "", "success": False, "dry_run": False, "error": "timeout"}
    except Exception as e:
        return {"content": "", "success": False, "dry_run": False, "error": str(e)}
    finally:
        try:
            os.unlink(prompt_file)
        except OSError:
            pass


def run_oracle(args: argparse.Namespace) -> dict[str, Any]:
    filepath = (ROOT / args.file).resolve() if not Path(args.file).is_absolute() else Path(args.file)
    if not filepath.exists():
        raise FileNotFoundError(filepath)

    if args.rounds != 1:
        logger.warning("fused safe mode sends one prompt; --rounds=%s is ignored", args.rounds)

    block = read_theorem_block(filepath, args.theorem)
    lean_check = compile_check(filepath, args.lean_timeout)
    prompt_profile, system_addendum = load_prompt_addendum(args.prompt_profile, args.system_prompt_file)

    prompt = build_oracle_prompt(
        filepath=filepath,
        theorem_name=args.theorem,
        theorem_block=block["theorem_block"],
        file_context=block["file_context"],
        lean_check=lean_check,
        system_addendum=system_addendum,
    )

    result = run_browser_harness(prompt, args.timeout)

    content = str(result.get("content") or "")
    candidate = extract_lean_code(content)
    readback_reason = response_readback_reason(content, candidate)
    if readback_reason:
        candidate = ""
    needs_readback = bool(result.get("suspect_intermediate")) or bool(readback_reason)

    report = {
        "file": str(filepath),
        "theorem": args.theorem,
        "prompt_profile": prompt_profile,
        "system_addendum_chars": len(system_addendum),
        "system_addendum_sha256": (
            __import__("hashlib").sha256(system_addendum.encode("utf-8")).hexdigest()
            if system_addendum
            else ""
        ),
        "lean_check": lean_check,
        "browser_result": result,
        "candidate_chars": len(candidate),
        "suspect_intermediate": bool(result.get("suspect_intermediate")),
        "response_contract_suspect": bool(readback_reason),
        "response_contract_reason": readback_reason,
        "needs_readback": needs_readback,
    }

    if args.response_out:
        out = Path(args.response_out)
        out.parent.mkdir(parents=True, exist_ok=True)
        out.write_text(content + ("\n" if content and not content.endswith("\n") else ""), encoding="utf-8")
    if args.candidate_out and candidate:
        out = Path(args.candidate_out)
        out.parent.mkdir(parents=True, exist_ok=True)
        out.write_text(candidate + "\n", encoding="utf-8")
    if args.json_out:
        write_json(Path(args.json_out), report)

    return report


def build_parser() -> argparse.ArgumentParser:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--file", required=True, help="Path to .lean owner file.")
    parser.add_argument("--theorem", required=True, help="Target theorem or lemma name.")
    parser.add_argument("--prompt-profile", default=None,
                        help="Optional additive oracle prompt profile from configs/oracle_prompt_profiles.")
    parser.add_argument("--system-prompt-file", default=None,
                        help="Optional additive prompt discipline file. Default prompt remains unchanged.")
    parser.add_argument("--timeout", type=int, default=300, help="Browser-harness message timeout in seconds.")
    parser.add_argument("--lean-timeout", type=int, default=120)
    parser.add_argument("--response-out", help="Write visible assistant response text.")
    parser.add_argument("--candidate-out", help="Write extracted Lean code candidate, if any.")
    parser.add_argument("--json-out", help="Write a JSON event report.")
    parser.add_argument("--json", action="store_true", help="Print full JSON report to stdout.")
    parser.add_argument("--quiet", action="store_true")
    parser.add_argument("--verbose", action="store_true")
    # Deprecated aiClaw options (kept for compatibility, ignored)
    parser.add_argument("--platform", default="chatgpt", help="Ignored (was aiClaw platform).")
    parser.add_argument("--base-url", default="", help="Ignored (was aiClaw base URL).")
    parser.add_argument("--rounds", type=int, default=1, help="Ignored (fused mode sends one prompt).")
    parser.add_argument("--wait-timeout", type=float, default=60, help="Ignored.")
    parser.add_argument("--interval", type=float, default=1, help="Ignored.")
    parser.add_argument("--no-login-required", action="store_true", help="Ignored.")
    parser.add_argument("--navigate", action="store_true", help="Ignored.")
    parser.add_argument("--no-new", action="store_true", help="Ignored.")
    parser.add_argument("--dry-run", action="store_true", help="Show send metadata without contacting ChatGPT.")
    parser.add_argument("--allow-sensitive", action="store_true", help="Ignored.")
    parser.add_argument("--no-queue", action="store_true", help="Ignored (no local queue with browser-harness).")
    parser.add_argument("--queue-root", default="", help="Ignored.")
    parser.add_argument("--queue-timeout", type=float, default=900, help="Ignored.")
    parser.add_argument("--no-hold-on-suspect", action="store_true", help="Ignored.")
    parser.add_argument("--pauli-platform", default=None, help="Deprecated; ignored.")
    return parser


def main() -> int:
    args = build_parser().parse_args()
    logging.basicConfig(
        level=logging.DEBUG if args.verbose else logging.INFO,
        format="%(asctime)s %(levelname)s [%(name)s] %(message)s",
    )
    if args.dry_run:
        print(json.dumps({"dry_run": True, "file": args.file, "theorem": args.theorem}, indent=2))
        return 0
    report = run_oracle(args)
    if args.json:
        print(json.dumps(report, indent=2, sort_keys=True))
    else:
        result = report["browser_result"]
        print(json.dumps({
            "success": bool(result.get("success", False)),
            "dry_run": False,
            "suspect_intermediate": report["suspect_intermediate"],
            "needs_readback": report["needs_readback"],
            "candidate_chars": report["candidate_chars"],
        }, indent=2, sort_keys=True))
    if report["needs_readback"]:
        return 2
    return 0 if report["browser_result"].get("success", False) else 1


if __name__ == "__main__":
    raise SystemExit(main())