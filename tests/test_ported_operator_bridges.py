from pathlib import Path

REPO = Path(__file__).resolve().parents[1]
CANONICAL = REPO / "lean" / "InfoGeometry" / "Canonical"
ALL = CANONICAL / "All.lean"


def test_operators_bridge_surface():
    text = (CANONICAL / "Operators.lean").read_text()

    assert "namespace InfoGeometry.Canonical.Operators" in text
    assert "noncomputable def operatorFreeEnergyReadout" in text
    assert "noncomputable def operatorFisherReadout" in text
    assert "noncomputable def operatorFisherDiagonal" in text
    assert "noncomputable def onsagerCoefficient" in text
    assert "theorem onsagerCoefficient_swap" in text
    assert "theorem entropyProduction_nonneg_of_probe_hessian_nonneg" in text


def test_operator_thermo_bridge_surface():
    text = (CANONICAL / "OperatorThermoBridge.lean").read_text()

    assert "namespace InfoGeometry.Canonical.OperatorThermoBridge" in text
    assert "noncomputable def operatorMassieuReadout" in text
    assert "noncomputable def operatorCanonicalEntropyProduction" in text
    assert "theorem operatorCanonicalEntropyProduction_eq_probe_hessian" in text
    assert "theorem scalarCanonicalFreeEnergy_sign" in text
    assert "theorem scalarCanonicalEntropy_sign" in text
    assert "theorem scalarCanonicalEnergy_sign" in text


def test_operatorial_fierz_bridge_surface():
    text = (CANONICAL / "OperatorialFierzBridge.lean").read_text()

    assert "namespace InfoGeometry.Canonical.OperatorialFierzBridge" in text
    assert "noncomputable def operatorTransportHilbertReadout" in text
    assert "noncomputable def operatorTransportSymplecticReadout" in text
    assert "noncomputable def transportEvaluatedFierzReadout" in text
    assert "theorem transportEvaluatedFierzReadout_fierzIdentity" in text
    assert "theorem transportEvaluatedFierzReadout_majorana" in text


def test_ported_operator_bridges_imported_by_all():
    text = ALL.read_text()

    assert "import InfoGeometry.Canonical.Operators" in text
    assert "import InfoGeometry.Canonical.OperatorThermoBridge" in text
    assert "import InfoGeometry.Canonical.OperatorialFierzBridge" in text
