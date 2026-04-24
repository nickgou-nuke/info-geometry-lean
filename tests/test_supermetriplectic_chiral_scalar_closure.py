from pathlib import Path
import re
import subprocess
import unittest
import os


REPO = Path(__file__).resolve().parents[1]
AXIOMS = REPO / "lean" / "InfoGeometry" / "SuperMetriplectic" / "Axioms.lean"


def has_decl(text: str, kind: str, name: str) -> bool:
    if kind == "def":
        pattern = rf"(?m)^\s*(?:noncomputable\s+)?def\s+{re.escape(name)}\b"
    else:
        pattern = rf"(?m)^\s*{kind}\s+{re.escape(name)}\b"
    return re.search(pattern, text) is not None


class SuperMetriplecticChiralScalarClosureTests(unittest.TestCase):
    def test_axioms_exposes_chiral_scalar_supercharge_surface(self) -> None:
        text = AXIOMS.read_text()
        self.assertTrue(has_decl(text, "structure", "ChiralSuperchargeClosure"))
        self.assertTrue(has_decl(text, "def", "netOddShadow"))
        self.assertTrue(has_decl(text, "theorem", "netOddShadow_eq_right_minus_left"))
        self.assertTrue(has_decl(text, "theorem", "anticommutator_netOddShadow_eq_translation_add_defect"))

    def test_supermetriplectic_axioms_builds_with_chiral_scalar_supercharge_surface(self) -> None:
        env = os.environ.copy()
        env["PATH"] = f"{Path.home() / '.elan' / 'bin'}:{env['PATH']}"
        cmd = [
            "python3",
            "tools/infra/run_locked_lake_build.py",
            "--wait-for-build-lock",
            "InfoGeometry.SuperMetriplectic.Axioms",
        ]
        subprocess.run(cmd, cwd=REPO, env=env, check=True)


if __name__ == "__main__":
    unittest.main()
