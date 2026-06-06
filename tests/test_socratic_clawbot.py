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
