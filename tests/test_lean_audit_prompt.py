from tools.infra.lean_audit_prompt import (
    build_findings_prompt,
    build_lean_fix_prompt,
    extract_replacement_lean,
)


def test_build_lean_fix_prompt_contains_anti_closure_rules():
    prompt = build_lean_fix_prompt(
        target_name="demo_theorem",
        context_code="def x := 1",
    )

    assert "ANTI-CONFABULATION / ANTI-OBFUSCATION RULES" in prompt
    assert "Lean compilation is not proof quality." in prompt
    assert "Missing proof has exactly one representation: `sorry`." in prompt
    assert "Do not invent bridge records" in prompt
    assert "If the theorem is open, say so plainly" in prompt
    assert "Open problems may be stated plainly." in prompt
    assert "BUCKET 1" not in prompt
    assert "BUCKET 2" not in prompt
    assert "BUCKET 3" not in prompt
    assert "full corrected Lean file content" in prompt
    assert "Keep the file small and mathlib-style" in prompt


def test_build_findings_prompt_uses_same_policy_block():
    prompt = build_findings_prompt(
        [{"file": "A.lean", "line": 1, "message": "error"}],
        {"B.lean": "def y := 2"},
    )

    assert "ANTI-CONFABULATION / ANTI-OBFUSCATION RULES" in prompt
    assert "BUCKET 2: CONDITIONAL THEOREMS FROM EXPLICIT THEOREM PARAMETERS" in prompt
    assert "Lean comments should name the missing owner declarations" in prompt
    assert "FILE: A.lean" in prompt
    assert "--- B.lean ---" in prompt


def test_extract_replacement_lean_prefers_canonical_full_file_block():
    response = """### Cause
bad rewrite

### Replacement
```lean4
import Mathlib

theorem demo : True := by
  trivial
```

### API
No API correction.
"""

    assert extract_replacement_lean(response) == "import Mathlib\n\ntheorem demo : True := by\n  trivial"
