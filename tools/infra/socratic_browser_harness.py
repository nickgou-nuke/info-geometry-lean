#!/usr/bin/env python3
"""
Jung-Pauli Socratic Proof Repair via ChatGPT Browser Harness (FREE — no API keys).

Runs inside `browser-harness -c` which provides browser globals:
    js(), new_tab(), wait_for_load(), goto_url()

Pipeline:
  1. Open ChatGPT temporary chat
  2. JUNG prompt: "You are the explorer. Think step-by-step. Generate a Lean 4 proof..."
     → Wait for full response
  3. PAULI prompt: "You are the critic. Find every flaw. If it compiles, say PASS..."
     → Wait for full response
  4. Optionally loop: send Pauli's feedback back to Jung
  5. Extract Lean code, compile check, write to file

Usage (inside browser-harness):
    browser-harness -c tools/infra/socratic_browser_harness.py \
        --theorem ModularCartanCantorSystem.coneVector_mem_naturalCone \
        --file lean/InfoGeometry/Canonical/ModularCartanCantorSystem.lean \
        --rounds 2

Requirements:
    - browser-harness installed (npm i -g browser-harness)
    - Chrome/Chromium running with remote debugging on port 9222
    - chatgpt.com accessible
"""

from __future__ import annotations

import json
import os
import re
import subprocess
import sys
import tempfile
import time
from pathlib import Path

# These are injected by browser-harness -c
# js, new_tab, wait_for_load, goto_url are globals in harness mode

_HERE = Path(__file__).resolve().parent
_REPO = _HERE.parents[1]
sys.path.insert(0, str(_REPO))

from tools.infra.chatgpt_lane_guard import browser_chatgpt_lane

CHATGPT_URL = os.environ.get("CHATGPT_URL", "https://chatgpt.com/?temporary-chat=true")
SENTINEL = "/tmp/chatgpt_socratic_tab_ready"
TIMEOUT = int(os.environ.get("CHATGPT_TIMEOUT_SECONDS", "600"))


# ---------------------------------------------------------------------------
# Browser helpers (only work inside browser-harness -c)
# ---------------------------------------------------------------------------

def _in_harness() -> bool:
    """Check if we're running inside browser-harness."""
    try:
        js("return true;")
        return True
    except Exception:
        return False


def _prompt_ready() -> bool:
    result = js("""(() => {
        const el = document.querySelector('textarea[aria-label*="Chat"], textarea, div[contenteditable="true"][role="textbox"], div[contenteditable="true"]');
        return !!el;
    })()""")
    return bool(result)


def _browser_send_state() -> dict:
    return js("""(() => {
        const buttonText = b => (b.getAttribute('aria-label') || '') + ' ' + (b.innerText || '');
        const buttons = Array.from(document.querySelectorAll('button'));
        const streaming = buttons.some(b => /Stop answering|Stop generating|Stop|Cancel|streaming/i.test(buttonText(b)));
        const fields = Array.from(document.querySelectorAll('textarea[aria-label*="Chat"], textarea, div[contenteditable="true"][role="textbox"], div[contenteditable="true"]'));
        const composerLengths = fields.map(el => {
            const text = el.tagName === 'TEXTAREA' ? el.value : (el.innerText || el.textContent || '');
            return text.length;
        });
        return {streaming, composerLengths};
    })()""")


def _assert_not_streaming() -> None:
    state = _browser_send_state()
    if state.get("streaming"):
        raise RuntimeError(
            "CHATGPT_LANE_BUSY: visible Stop/Cancel/streaming control is present; "
            "recover the final visible answer before sending another prompt"
        )


def _assert_composer_empty() -> None:
    state = _browser_send_state()
    lengths = state.get("composerLengths") or []
    if any(int(length) > 0 for length in lengths):
        raise RuntimeError(
            "CHATGPT_COMPOSER_NOT_EMPTY: refusing to overwrite an unsent prompt; "
            f"composer_lengths={lengths}"
        )


def _open_chatgpt():
    if os.path.exists(SENTINEL):
        current = js("return window.location.href;")
        if "chatgpt.com" not in str(current):
            goto_url(CHATGPT_URL)
            wait_for_load()
    else:
        print(f"Opening {CHATGPT_URL}...")
        new_tab(CHATGPT_URL)
        wait_for_load()
        open(SENTINEL, "w").close()
    time.sleep(2)
    if not _prompt_ready():
        os.unlink(SENTINEL)
        new_tab(CHATGPT_URL)
        wait_for_load()
        open(SENTINEL, "w").close()
        time.sleep(2)
    # Wait until prompt field appears
    deadline = time.time() + 30
    while time.time() < deadline:
        if _prompt_ready():
            break
        time.sleep(1)
    print("ChatGPT tab ready.")


def _send_message(text: str):
    """Type text into ChatGPT and send."""
    print(f"Sending message ({len(text)} chars)...")
    _assert_not_streaming()
    _assert_composer_empty()

    # Insert text into the prompt field
    result = js(f"""(() => {{
        const prompt = {json.dumps(text)};
        const box = document.querySelector('div[contenteditable="true"]');
        const ta = document.querySelector('textarea');
        const fire = (el) => {{
            el.dispatchEvent(new InputEvent('input', {{bubbles:true, inputType:'insertText', data: prompt}}));
            el.dispatchEvent(new Event('change', {{bubbles:true}}));
        }};
        if (box) {{ box.focus(); box.textContent = prompt; fire(box); return 'box'; }}
        if (ta) {{
            const setter = Object.getOwnPropertyDescriptor(window.HTMLTextAreaElement.prototype, 'value').set;
            setter.call(ta, prompt); ta.focus(); fire(ta); return 'textarea';
        }}
        return 'none';
    }})()""")

    # Click the real send button. Do not fake Enter: if the button is missing,
    # the prompt was not recognized or ChatGPT is busy.
    deadline = time.time() + 10
    submit = {"ok": False, "reason": "not_started"}
    while time.time() < deadline:
        _assert_not_streaming()
        submit = js("""(() => {
            const btn = Array.from(document.querySelectorAll('button')).find(b =>
                !b.disabled && (/send-button/i.test(b.getAttribute('data-testid') || '') ||
                  /Send/i.test((b.getAttribute('aria-label') || '') + ' ' + (b.innerText || ''))));
            if (btn) { btn.click(); return {ok:true, via:'button'}; }
            const fields = Array.from(document.querySelectorAll('textarea[aria-label*="Chat"], textarea, div[contenteditable="true"][role="textbox"], div[contenteditable="true"]'));
            const composerLengths = fields.map(el => {
                const text = el.tagName === 'TEXTAREA' ? el.value : (el.innerText || el.textContent || '');
                return text.length;
            });
            return {ok:false, reason:'send_button_missing', composerLengths};
        })()""")
        if submit.get("ok"):
            break
        time.sleep(0.5)
    if not submit.get("ok"):
        raise RuntimeError(f"failed to submit prompt: {submit}")

    print(f"Prompt inserted via {result}; sent via {submit.get('via')}")


def _streaming() -> bool:
    return bool(js("""Array.from(document.querySelectorAll('button'))
        .some(b => /Stop|streaming/i.test((b.getAttribute('aria-label')||'')+' '+(b.innerText||'')))"""))


def _get_response() -> str:
    """Wait for ChatGPT to finish streaming, return the last assistant message."""
    deadline = time.time() + TIMEOUT
    while time.time() < deadline:
        msgs = js("""JSON.stringify(Array.from(
            document.querySelectorAll('[data-message-author-role="assistant"]')
        ).map(e => e.innerText || ''))""")
        try:
            messages = json.loads(msgs)
        except Exception:
            messages = []
        streaming = _streaming()
        if messages and not streaming:
            last = messages[-1].strip()
            if last:
                print(f"Response received ({len(last)} chars)")
                return last
        print(f"Waiting... (messages: {len(messages)}, streaming: {streaming})")
        time.sleep(3)

    # Timeout — return whatever we have
    msgs = js("""JSON.stringify(Array.from(
        document.querySelectorAll('[data-message-author-role="assistant"]')
    ).map(e => e.innerText || ''))""")
    try:
        messages = json.loads(msgs)
        return messages[-1] if messages else "TIMEOUT"
    except Exception:
        return "TIMEOUT"


# ---------------------------------------------------------------------------
# Jung & Pauli prompts
# ---------------------------------------------------------------------------

def jung_prompt(theorem_block: str, file_context: str, google_context: str = "") -> str:
    return f"""You are the JUNG explorer — the creative mathematician who generates candidate proofs.
Think step-by-step. Reason deeply. Consider multiple approaches before committing.

## TARGET THEOREM

```lean4
{theorem_block}
```

## FILE CONTEXT (imports and surrounding definitions)

```lean4
{file_context}
```

{f"## EXTERNAL CONTEXT\n\n{google_context}" if google_context else ""}

## INSTRUCTIONS

1. Read the theorem statement carefully. What is it asserting?
2. What structures and hypotheses are available? List them.
3. What mathlib4 theorems could help? Name specific lemmas if you know them.
4. Write a complete Lean 4 proof replacing `:= by sorry`.
5. Output the proof in ```lean4 ... ``` fences.
6. If you cannot complete the proof, output the best partial proof with an honest `sorry`.
7. Do NOT change the theorem statement or name."""


def pauli_prompt(theorem_block: str, jung_response: str) -> str:
    return f"""You are the PAULI adjudicator — the ruthless critic who finds every flaw.

## ORIGINAL THEOREM

```lean4
{theorem_block}
```

## JUNG'S PROPOSED PROOF

{jung_response[:3000]}

## INSTRUCTIONS

1. Does the proof actually compile? Check every type, every binder, every tactic.
2. Are there hidden assumptions not discharged?
3. Is there any `sorry`, `admit`, `trivial`, or `rfl` on a non-definitional equality?
4. Is there a circular dependency?
5. What would make this proof FAIL?

Output in this EXACT format:
```
VERDICT: PASS or FAIL

If PASS:
  CONFIRMATION: <why the proof is valid>

If FAIL:
  OBSTRUCTION: <exact obstruction term>
  MISSING: <what hypothesis or lemma is missing>
  FIX: <suggested fix, or "NONE — proof is fundamentally wrong">
```

Be specific. Name exact Lean types and terms. Do not soften your critique."""


def jung_repair_prompt(theorem_block: str, pauli_critique: str, previous_proof: str) -> str:
    return f"""You are JUNG again. Pauli has found flaws in your proof. Fix them.

## TARGET THEOREM

```lean4
{theorem_block}
```

## YOUR PREVIOUS PROOF

```lean4
{previous_proof[:2000]}
```

## PAULI'S CRITIQUE

{pauli_critique[:2000]}

## INSTRUCTIONS

1. Address EVERY obstruction Pauli identified.
2. If Pauli said PASS, confirm and output the final proof.
3. If Pauli identified a missing lemma, try to prove it inline or note it as a new sorry.
4. Output the corrected proof in ```lean4 ... ``` fences."""


# ---------------------------------------------------------------------------
# Lean compilation
# ---------------------------------------------------------------------------

def extract_lean_code(text: str) -> str:
    """Extract Lean 4 code block from response."""
    m = re.search(r"```(?:lean4|lean)?\s*\n(.*?)```", text, re.DOTALL)
    if m:
        return m.group(1).strip()
    # Fallback: find theorem block
    m = re.search(r"(theorem\s+\w+.*?:=.*?)(?=\n\s*(?:theorem|lemma|def|end|namespace|$))",
                  text, re.DOTALL)
    if m:
        return m.group(1).strip()
    return ""


def compile_check(lean_file: Path) -> dict:
    proc = subprocess.run(["lake", "env", "lean", str(lean_file)],
                          cwd=_REPO, capture_output=True, text=True, timeout=120)
    return {
        "success": proc.returncode == 0,
        "error": (proc.stderr or proc.stdout)[-3000:],
    }


# ---------------------------------------------------------------------------
# Main socratic loop
# ---------------------------------------------------------------------------

def run_socratic_harness(
    filepath: Path,
    theorem_name: str,
    rounds: int = 2,
) -> dict:
    """Run Jung-Pauli dialogue via browser-harness ChatGPT."""
    if not _in_harness():
        print("ERROR: This script must be run inside browser-harness:")
        print("  browser-harness -c tools/infra/socratic_browser_harness.py --theorem X --file Y")
        sys.exit(1)

    with browser_chatgpt_lane(
        source="socratic_browser_harness",
        platform="chatgpt",
        prompt_chars=None,
        reason="socratic_browser_harness_dialogue",
    ):
        return _run_socratic_harness_locked(filepath, theorem_name, rounds)


def _run_socratic_harness_locked(
    filepath: Path,
    theorem_name: str,
    rounds: int = 2,
) -> dict:
    _open_chatgpt()

    # Read the target theorem and file context
    text = filepath.read_text(encoding="utf-8")
    lines = text.split("\n")

    # Find the theorem
    theorem_re = re.compile(rf"^\s*(@\[[^\]]*\])?\s*theorem\s+{re.escape(theorem_name)}\b")
    start_line = None
    for i, line in enumerate(lines):
        if theorem_re.search(line):
            start_line = i
            break
    if start_line is None:
        print(f"ERROR: Theorem '{theorem_name}' not found in {filepath}")
        sys.exit(1)

    # Find the end
    end_re = re.compile(r"^\s*(?:theorem|lemma|def|structure|inductive|class|end|namespace|section|abbrev)\b")
    end_line = len(lines)
    for i in range(start_line + 1, len(lines)):
        if end_re.search(lines[i]):
            end_line = i
            break

    theorem_block = "\n".join(lines[start_line:end_line])
    file_context = "\n".join(lines[max(0, start_line - 30):start_line])  # 30 lines of context

    print(f"\n{'='*60}")
    print(f"  JUNG-PAULI SOCRATIC PROOF REPAIR")
    print(f"  Theorem: {theorem_name}")
    print(f"  Rounds: {rounds}")
    print(f"{'='*60}\n")

    current_proof = ""
    pauli_feedback = ""

    for r in range(1, rounds + 1):
        print(f"\n--- Round {r}/{rounds} ---")

        # JUNG TURN
        if r == 1:
            prompt = jung_prompt(theorem_block, file_context)
        else:
            prompt = jung_repair_prompt(theorem_block, pauli_feedback, current_proof)

        print(f"JUNG: Sending prompt ({len(prompt)} chars)...")
        _send_message(prompt)
        jung_response = _get_response()
        print(f"JUNG: Got response ({len(jung_response)} chars)")

        lean_code = extract_lean_code(jung_response)
        if lean_code:
            print(f"JUNG: Extracted Lean code ({len(lean_code)} chars)")
            current_proof = lean_code
        else:
            print("JUNG: No Lean code block found in response")

        # PAULI TURN
        pauli_text = pauli_prompt(theorem_block, jung_response)
        print(f"PAULI: Sending critique prompt ({len(pauli_text)} chars)...")
        _send_message(pauli_text)
        pauli_response = _get_response()
        print(f"PAULI: Got critique ({len(pauli_response)} chars)")
        pauli_feedback = pauli_response

        # Check if Pauli says PASS
        if re.search(r'\bPASS\b', pauli_response, re.IGNORECASE) and \
           not re.search(r'\bFAIL\b', pauli_response, re.IGNORECASE):
            print("PAULI: VERDICT = PASS")
        else:
            # Extract obstruction
            obs_match = re.search(r'OBSTRUCTION:\s*(.+?)(?:\n|$)', pauli_response, re.IGNORECASE)
            if obs_match:
                print(f"PAULI: Obstruction: {obs_match.group(1)[:100]}")

    # Final: compile check
    if current_proof:
        # Write the proof into the file and compile
        new_content = (
            "\n".join(lines[:start_line]) + "\n" +
            current_proof + "\n" +
            "\n".join(lines[end_line:])
        )

        print(f"\n{'='*60}")
        print(f"  COMPILE CHECK")
        print(f"{'='*60}")

        with tempfile.NamedTemporaryFile(mode="w", suffix=".lean", delete=False,
                                         dir="/tmp", encoding="utf-8") as f:
            f.write(new_content)
            tmp_path = Path(f.name)

        result = compile_check(tmp_path)
        tmp_path.unlink()

        if result["success"]:
            print("COMPILE SUCCESS!")
            # Write back to the real file
            filepath.write_text(new_content, encoding="utf-8")
            print(f"Written to {filepath}")
            return {"success": True, "proof": current_proof, "rounds": r if 'r' in dir() else rounds}
        else:
            print(f"COMPILE FAILED:")
            # Show first few error lines
            for line in result["error"].split("\n")[:5]:
                if line.strip():
                    print(f"  {line.strip()[:150]}")
            return {"success": False, "error": result["error"][:2000], "rounds": r if 'r' in dir() else rounds}

    return {"success": False, "error": "No proof produced", "rounds": rounds}


# ---------------------------------------------------------------------------
# CLI
# ---------------------------------------------------------------------------

if __name__ == "__main__":
    import argparse
    parser = argparse.ArgumentParser(description="Jung-Pauli Socratic Proof Repair (browser-harness)")
    parser.add_argument("--file", required=True, help="Path to .lean file")
    parser.add_argument("--theorem", required=True, help="Theorem name")
    parser.add_argument("--rounds", type=int, default=2, help="Jung-Pauli exchange rounds")
    parser.add_argument("--google", help="Optional Google AI search query for context")
    args = parser.parse_args()

    filepath = _REPO / args.file if not args.file.startswith("/") else Path(args.file)

    result = run_socratic_harness(filepath, args.theorem, args.rounds)
    print(f"\nFinal: {'PASS' if result['success'] else 'FAIL'} after {result['rounds']} rounds")
