from pathlib import Path
import re


REPO = Path(__file__).resolve().parents[1]
TARGET = REPO / "lean" / "InfoGeometry" / "Canonical" / "SuperSouriauFermionGasBridge.lean"


def test_identity_balanced_stress_constructor_and_theorem_are_live_declarations() -> None:
    text = TARGET.read_text(encoding="utf-8")

    assert re.search(r"(?m)^\s*structure\s+BalancedScalarStress\b", text)
    assert re.search(r"(?m)^\s*def\s+WeylSupertraceFreeStressContext\.ofIdentityBalanced\b", text)
    assert re.search(r"(?m)^\s*theorem\s+superTrace_eq_zero_ofIdentityBalanced\b", text)
