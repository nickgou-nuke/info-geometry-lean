from tools.infra.aiclaw_audit_runner import extract_lean_code, repair_column_zero_tactic_layout


def test_extract_lean_code_prefers_fenced_lean_block() -> None:
    response = """### Replacement
```lean4
import Mathlib

#check Nat
```
"""

    assert extract_lean_code(response) == "import Mathlib\n\n#check Nat\n"


def test_repair_column_zero_calc_block() -> None:
    broken = """import Mathlib

theorem demo : (1 : Nat) = 1 := by
calc
1 = 1 := by
rfl
"""

    repaired = repair_column_zero_tactic_layout(broken)

    assert """theorem demo : (1 : Nat) = 1 := by
  calc
    1 = 1 := by
      rfl
""" in repaired


def test_repair_column_zero_tactic_body_keeps_next_theorem_top_level() -> None:
    broken = """theorem first : True := by
trivial

theorem second : True := by
trivial
"""

    repaired = repair_column_zero_tactic_layout(broken)

    assert repaired == """theorem first : True := by
  trivial

theorem second : True := by
  trivial
"""


def test_repair_column_zero_tactic_layout_preserves_indented_code() -> None:
    original = """theorem demo : True := by
  trivial
"""

    assert repair_column_zero_tactic_layout(original) == original
