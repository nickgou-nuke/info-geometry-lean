#!/usr/bin/env python3
"""
Semantic Proof Auditor — LLM-based critique of generated proofs.

Takes ChatGPT output and semantically classifies it:
  - genuine: proof derives from real definitions + Mathlib
  - cheating: wrapper closure, theorem-as-data, projection proof
  - incomplete: contains sorry, but honestly
  - fake: reference to non-existent lemmas, invented imports

Also extracts NEW anti-patterns for the LeanTrail audit dictionary.
"""
from __future__ import annotations
import json, logging, os, re, subprocess, tempfile, sys
from pathlib import Path

_HERE = Path(__file__).resolve().parent
_REPO = _HERE.parents[1]
sys.path.insert(0, str(_REPO))

logger = logging.getLogger("proof_auditor")

CHATGPT_SCRIPT = _REPO / "tools" / "infra" / "chatgpt_browser_harness_driver.py"
AUDIT_PROMPT = """SEMANTIC PROOF AUDIT

You are a mathematical proof auditor. Analyze the following Lean 4 code and classify it.

Output a JSON object with these fields:
{
  "verdict": "genuine" | "cheating" | "incomplete" | "fake",
  "confidence": 0.0-1.0,
  "reasons": ["list of specific reasons"],
  "anti_patterns": ["new anti-patterns discovered"],
  "genuine_parts": ["parts that are real mathematics"],
  "fake_parts": ["parts that are fake/synthetic"]
}

Classification criteria:
- "genuine": proof derives from real definitions in Mathlib or the file. No projection proofs, no theorem-as-data.
- "cheating": uses wrapper closure (projecting from a structure field), theorem-as-data (Prop fields to re-read the theorem), fake imports, or certificate patterns.
- "incomplete": contains honest `sorry` but the structure is correct.
- "fake": references non-existent lemmas, invented imports, hallucinated theorem names.

ANTI-PATTERNS TO WATCH FOR:
1. `exact B.h` — proof by projection from a structure field
2. `simpa using B.h` — same, disguised
3. `_True : Prop := ...` — theorem-as-data
4. `_sorryProof` — certificate wrapper
5. Non-existent Mathlib imports
6. Redefining the target to make it trivial
7. Proving a weaker/unrelated theorem instead of the target

CODE TO AUDIT:
```lean4
{code}
```

Output ONLY the JSON object. No prose."""


def audit_proof(code: str, timeout: int = 120) -> dict:
    """Send code to ChatGPT for semantic audit, return classification."""
    prompt = AUDIT_PROMPT.replace("{code}", code[:8000])
    pf = tempfile.NamedTemporaryFile(mode='w', suffix='.txt', delete=False)
    pf.write(prompt); pf.close()
    rf = tempfile.NamedTemporaryFile(mode='w', suffix='.json', delete=False)
    rf.close()

    env = os.environ.copy()
    env['CHATGPT_PROMPT_FILE'] = pf.name
    env['CHATGPT_RESULT_JSON'] = rf.name
    env['CHATGPT_TIMEOUT_SECONDS'] = str(timeout)

    subprocess.run(
        ['browser-harness', '-c',
         f"import sys; sys.path.insert(0,'{_REPO}'); exec(open('{CHATGPT_SCRIPT}').read()); _main()"],
        env=env, capture_output=True, text=True, timeout=timeout + 60,
    )
    result = open(rf.name).read() if Path(rf.name).exists() else ""
    os.unlink(pf.name); os.unlink(rf.name)

    try:
        m = re.search(r'\{[\s\S]*\}', result)
        return json.loads(m.group()) if m else {"verdict": "unknown", "reasons": [result[:200]]}
    except json.JSONDecodeError:
        return {"verdict": "unknown", "reasons": [result[:200]]}


def expand_anti_patterns(audits: list[dict]) -> list[str]:
    """Collect new anti-patterns from multiple audits."""
    patterns = []
    for a in audits:
        for p in a.get("anti_patterns", []):
            if p not in patterns:
                patterns.append(p)
    return patterns


if __name__ == "__main__":
    import argparse
    p = argparse.ArgumentParser()
    p.add_argument("--code-file", help="Lean file to audit")
    p.add_argument("--code", help="Lean code string to audit")
    args = p.parse_args()
    logging.basicConfig(level=logging.INFO, format="%(asctime)s %(message)s")

    code = ""
    if args.code_file:
        code = Path(args.code_file).read_text()
    elif args.code:
        code = args.code
    else:
        code = sys.stdin.read()

    result = audit_proof(code)
    print(json.dumps(result, indent=2))
