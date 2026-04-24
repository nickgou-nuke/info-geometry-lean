from pathlib import Path


REPO = Path(__file__).resolve().parents[1]
SOURCE = REPO / "lean" / "InfoGeometry" / "Canonical" / "DrazinSupercharge.lean"
BRIDGE = REPO / "lean" / "InfoGeometry" / "Canonical" / "ClosureDrazinBridge.lean"


def test_drazin_chiral_supertrace_owner_is_operatorial_not_dixmier() -> None:
    text = SOURCE.read_text(encoding="utf-8")

    assert "structure ChiralSupertraceReadout" in text
    assert "def chiralSupertrace" in text
    assert "theorem chiralSupertrace_supercharge_eq_zero" in text
    assert "supercharge_mul_GammaS_eq_neg" in text

    owner_block = text.split("Chiral supertrace readout", 1)[1].split(
        "theorem superHamiltonian_commutes_GammaS", 1
    )[0]
    assert "Dixmier" in owner_block
    assert "not a Dixmier trace" in owner_block
    assert "Witten" in owner_block
    assert "Pfaffian" in owner_block
    assert "Macaev" not in owner_block
    assert "Type III" not in owner_block


def test_closure_drazin_bridge_exports_chiral_supertrace_owner_theorem() -> None:
    text = BRIDGE.read_text(encoding="utf-8")

    assert "theorem chiralSupertrace_supercharge_eq_zero" in text
    assert "DrazinSupercharge.CertifiedInverseKernel.chiralSupertrace_supercharge_eq_zero" in text
    assert "DrazinSupercharge.CertifiedInverseKernel.ChiralSupertraceReadout" in text
