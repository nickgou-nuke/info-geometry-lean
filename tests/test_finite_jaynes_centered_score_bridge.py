from pathlib import Path
import os
import re
import subprocess


REPO = Path(__file__).resolve().parents[1]
CANONICAL = REPO / "lean" / "InfoGeometry" / "Canonical"
SOURCE = CANONICAL / "FiniteJaynesCenteredScoreBridge.lean"
CANONICAL_ALL = CANONICAL / "All.lean"


def has_decl(text: str, kind: str, name: str) -> bool:
    pattern = rf"(?m)^\s*(?:noncomputable\s+)?{kind}\s+{re.escape(name)}\b"
    return re.search(pattern, text) is not None


def test_finite_jaynes_centered_score_surface_exists() -> None:
    assert SOURCE.exists(), f"missing file: {SOURCE}"
    text = SOURCE.read_text(encoding="utf-8")
    assert "namespace InfoGeometry.Canonical.FiniteJaynesCenteredScoreBridge" in text
    assert has_decl(text, "abbrev", "FiniteProfile")
    assert has_decl(text, "structure", "FiniteReferenceState")
    assert has_decl(text, "structure", "FiniteJaynesPair")
    assert has_decl(text, "def", "relativeDensity")
    assert has_decl(text, "def", "centeredRelativeDensity")
    assert has_decl(text, "theorem", "centeredRelativeDensity_self")
    assert has_decl(text, "theorem", "relativeDensity_eq_one_add_centered")
    assert has_decl(text, "theorem", "ref_weighted_centeredRelativeDensity_eq_mass_sub")
    assert has_decl(text, "theorem", "ref_weighted_centeredRelativeDensity_eq_zero_of_equal_mass")


def test_finite_jaynes_centered_score_boundary_hygiene() -> None:
    text = SOURCE.read_text(encoding="utf-8")
    forbidden = [
        "spectralTheorem",
        "projectionValuedMeasure",
        "PVM",
        "weakStar",
        "HaagKastler",
        "hyperfiniteII1",
        "TypeIII",
        "globalDiracSeaReconstruction",
    ]
    for token in forbidden:
        assert token not in text
    assert "sorry" not in text
    assert "admit" not in text
    assert "axiom" not in text
    assert "Nonempty" not in text


def test_canonical_all_imports_finite_jaynes_centered_score_bridge() -> None:
    text = CANONICAL_ALL.read_text(encoding="utf-8")
    assert "import InfoGeometry.Canonical.FiniteJaynesCenteredScoreBridge" in text


def test_finite_jaynes_centered_score_bridge_builds() -> None:
    env = os.environ.copy()
    env["PATH"] = f"{Path.home() / '.elan' / 'bin'}:{env['PATH']}"
    subprocess.run(
        [
            "python3",
            "tools/infra/run_locked_lake_build.py",
            "--wait-for-build-lock",
            "InfoGeometry.Canonical.FiniteJaynesCenteredScoreBridge",
        ],
        cwd=REPO,
        env=env,
        check=True,
    )
