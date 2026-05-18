from pathlib import Path


REPO = Path(__file__).resolve().parents[1]
SOURCE = REPO / "lean" / "InfoGeometry" / "Canonical" / "BoundedKMSConditionBridge.lean"


def test_minimal_bounded_kms_condition_context_internalizes_state_and_boundary_packet() -> None:
    text = SOURCE.read_text(encoding="utf-8")

    struct_anchor = "structure MinimalBoundedKMSConditionBridge where"
    assert struct_anchor in text
    struct_block = text.split(struct_anchor, 1)[1].split(
        "namespace MinimalBoundedKMSConditionBridge", 1
    )[0]
    assert "state :" not in struct_block
    assert "KMSAnalyticCertificate" not in struct_block
    assert "kms :" in struct_block
    assert "KMSState EndH" in struct_block

    assert "def toBoundedKMSConditionBridge" in text
    adapter_block = text.split("def toBoundedKMSConditionBridge", 1)[1].split(
        "/-- The bounded modular flow as a plain operator-thermodynamic flow datum. -/", 1
    )[0]
    assert "state := B.kms.state" in adapter_block
    assert "kms := B.kms.kms" in adapter_block

    assert "theorem state_eq_kms_state" in text
    assert "theorem kms_boundary_holds" in text


def test_broad_bounded_kms_bridge_has_flow_invariant_route_to_minimal_context() -> None:
    text = SOURCE.read_text(encoding="utf-8")

    assert "def toMinimalBoundedKMSConditionBridge" in text
    def_block = text.split("def toMinimalBoundedKMSConditionBridge", 1)[1].split(
        "theorem toMinimalBoundedKMSConditionBridge_state_eq", 1
    )[0]
    assert "(hInvariant :" in def_block
    assert "state := B.state" in def_block
    assert "flow_invariant := hInvariant" in def_block
    assert "kms := B.kms" in def_block

    assert "theorem toMinimalBoundedKMSConditionBridge_of_flow_invariant" in text
    theorem_block = text.split(
        "theorem toMinimalBoundedKMSConditionBridge_of_flow_invariant", 1
    )[1].split("end BoundedKMSConditionBridge", 1)[0]
    assert "∃ M : MinimalBoundedKMSConditionBridge" in theorem_block
    assert "B.toMinimalBoundedKMSConditionBridge hInvariant" in theorem_block

    assert "theorem toMinimalBoundedKMSConditionBridge_state_eq" in text
    assert "theorem toMinimalBoundedKMSConditionBridge_toBoundedKMSConditionBridge" in text
