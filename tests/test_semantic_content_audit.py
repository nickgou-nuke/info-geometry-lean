from tools.quality.semantic_content_audit import semantic_status


def test_proof_hole_blocks_before_other_categories() -> None:
    status, action = semantic_status({"proof-hole", "trivial-theorem"})

    assert status == "proof_hole_blocker"
    assert "quarantine" in action


def test_axiom_is_assumption_bearing_blocker() -> None:
    status, action = semantic_status({"axiom"})

    assert status == "explicit_axiom_blocker"
    assert "hypothesis context" in action


def test_trivial_true_surface_is_vacuous_review_not_canonical() -> None:
    status, action = semantic_status({"prop-constant", "trivial-theorem"})

    assert status == "vacuous_or_surrogate_surface"
    assert "True/trivial" in action


def test_clean_surface_is_only_clean_by_this_audit() -> None:
    status, action = semantic_status(set())

    assert status == "content_clean_by_this_audit"
    assert "this audit" in action
