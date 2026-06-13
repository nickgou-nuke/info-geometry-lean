from tools.infra.aiclaw_audit_runner import extract_lean_code as extract_aiclaw_lean_code
from tools.infra.lean_audit_prompt import lean_candidate_reject_reason
from tools.infra.socratic_clawbot import extract_lean_code, response_readback_reason


def test_response_readback_reason_flags_flattened_replacement_payload():
    response = (
        "Cause\n"
        "The proof already compiles.\n"
        "Replacement\n"
        "lean4import Mathlibopen scoped Matrix"
        "namespace Demo theorem t : True := by trivial end Demo\n"
        "API\n"
        "No API correction."
    )
    candidate = extract_lean_code(response)

    assert candidate == ""
    assert response_readback_reason(response, candidate) == "replacement_section_missing_code_fence"


def test_response_readback_reason_accepts_no_replacement_needed():
    response = """### Cause
The file already checks.

### Replacement
no replacement needed

### API
No API correction.
"""

    assert response_readback_reason(response, "") == ""


def test_clarification_prose_is_rejected_as_candidate():
    response = (
        "Could you clarify which file has the error? "
        "SelfDualNormalConeBridge.lean doesn't exist in this repo."
    )
    candidate = extract_lean_code(response)

    assert candidate == ""
    assert response_readback_reason(response, candidate) == "natural_language_candidate"
    assert lean_candidate_reject_reason(response, allow_snippet=True) == "natural_language_candidate"


def test_aiclaw_runner_does_not_treat_raw_prose_as_lean_file():
    response = (
        "The code you pasted is from another file. "
        "Please share the actual error message and file path."
    )

    assert extract_aiclaw_lean_code(response) == ""


def test_lean_candidate_guard_accepts_real_snippet():
    assert lean_candidate_reject_reason("by\n  exact h", allow_snippet=True) == ""
