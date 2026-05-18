from pathlib import Path
import re

REPO = Path(__file__).resolve().parents[1]
SOURCE = REPO / "lean" / "InfoGeometry" / "Arithmetic" / "PrimeFiniteArithmeticDictionary.lean"
ALL = REPO / "lean" / "InfoGeometry" / "All.lean"


def test_prime_finite_arithmetic_dictionary_is_finite_only() -> None:
    assert SOURCE.exists(), "Missing finite bridge module: PrimeFiniteArithmeticDictionary.lean"
    text = SOURCE.read_text(encoding="utf-8")

    # Finite owner surfaces must be the only inputs.
    for needle in [
        "import InfoGeometry.Arithmetic.PrimeBooleanCube",
        "import InfoGeometry.Arithmetic.PrimeMajoranaCAR",
        "import InfoGeometry.Arithmetic.PrimeMajoranaDiracFinite",
        "import InfoGeometry.Arithmetic.PrimeExteriorRepresentation",
        "theorem carParity_readout_eq_booleanLocalParity",
        "theorem carGlobalChiralityReadout_eq_booleanChirality",
        "theorem carGlobalChiralityReadout_eq_fermionParity",
        "theorem carGlobalChiralityReadout_eq_mobius",
        "theorem finiteDiracHamiltonian_dictionary",
        "theorem exteriorGamma_eq_booleanChirality",
        "theorem exteriorMobius_eq_booleanMöbius",
        "def PrimeFiniteArithmeticDictionaryOwnerTarget",
        "theorem primeFiniteArithmeticDictionaryOwnerTarget",
        "@[owner_target_tag]",
        "@[bridge_target_tag",
    ]:
        assert needle in text, f"missing expected finite bridge anchor: {needle}"

    # Hard boundary: no analytic / RH claims in the executable code.
    # The docstring intentionally states the negative boundary in plain English,
    # so strip comments before checking for leakage.
    code = re.sub(r"/-!.*?-/", "", text, flags=re.S)
    code = re.sub(r"/-.*?-/", "", code, flags=re.S)
    code = re.sub(r"--.*$", "", code, flags=re.M)
    forbidden = [
        "Euler product",
        "Euler-product",
        "analytic continuation",
        "RH",
        "Riemann Hypothesis",
        "Lee-Yang",
        "Lee--Yang",
        "Hilbert-Pólya",
        "Hilbert-Polya",
    ]
    for needle in forbidden:
        assert needle not in code, f"forbidden analytic/RH leakage found in finite bridge module: {needle}"


def test_prime_finite_arithmetic_dictionary_is_in_umbrella() -> None:
    assert ALL.exists(), "Missing umbrella file: InfoGeometry.All.lean"
    text = ALL.read_text(encoding="utf-8")
    assert "import InfoGeometry.Arithmetic.PrimeFiniteArithmeticDictionary" in text
