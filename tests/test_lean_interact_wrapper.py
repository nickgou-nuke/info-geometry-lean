from tools.infra.lean_interact_wrapper import apply_tactic, get_proof_state


def test_get_proof_state_reports_goal():
    result = get_proof_state("1 = 1", imports=["Init"], timeout=30)

    assert result["status"] == "ok"
    assert "⊢ 1 = 1" in result["proof_state"]


def test_apply_tactic_accepts_valid_tactic():
    result = apply_tactic("1 = 1", "rfl", imports=["Init"], timeout=30)

    assert result["status"] == "success"
    assert result["lean"]["ok"] is True
    assert "⊢ 1 = 1" in result["proof_state_before"]


def test_apply_tactic_rejects_invalid_tactic():
    result = apply_tactic("1 = 1", "exact 0", imports=["Init"], timeout=30)

    assert result["status"] == "failure"
    assert result["lean"]["ok"] is False
    output = result["lean"]["stdout"] + result["lean"]["stderr"]
    assert "error:" in output
