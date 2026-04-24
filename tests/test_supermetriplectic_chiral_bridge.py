from pathlib import Path
import re
import subprocess
import unittest
import os


REPO = Path(__file__).resolve().parents[1]
BRIDGE = REPO / "lean" / "InfoGeometry" / "SuperMetriplectic" / "ChiralBridge.lean"
ALL = REPO / "lean" / "InfoGeometry" / "SuperMetriplectic" / "All.lean"


def has_decl(text: str, kind: str, name: str) -> bool:
    if kind == "def":
        pattern = rf"(?m)^\s*(?:noncomputable\s+)?def\s+{re.escape(name)}\b"
    else:
        pattern = rf"(?m)^\s*{kind}\s+{re.escape(name)}\b"
    return re.search(pattern, text) is not None


class SuperMetriplecticChiralBridgeTests(unittest.TestCase):
    def test_bridge_surface_exists(self) -> None:
        bridge_text = BRIDGE.read_text(encoding="utf-8")
        all_text = ALL.read_text(encoding="utf-8")

        self.assertIn("import InfoGeometry.SuperMetriplectic.ChiralBridge", all_text)
        self.assertTrue(has_decl(bridge_text, "structure", "DrazinChiralSuperchargeClosureBridge"))
        self.assertTrue(has_decl(bridge_text, "def", "toChiralSuperchargeClosure"))
        self.assertTrue(has_decl(bridge_text, "theorem", "toChiralSuperchargeClosure_leftShadow_eq_QL"))
        self.assertTrue(has_decl(bridge_text, "theorem", "toChiralSuperchargeClosure_rightShadow_eq_QR"))
        self.assertTrue(has_decl(bridge_text, "theorem", "toChiralSuperchargeClosure_netOddShadow_eq_QD"))
        self.assertTrue(has_decl(bridge_text, "theorem", "toChiralSuperchargeClosure_translationShadow_eq_drazinTranslationCandidate"))
        self.assertTrue(has_decl(bridge_text, "theorem", "toChiralSuperchargeClosure_defectShadow_eq_drazinCentralCandidate"))
        self.assertTrue(has_decl(bridge_text, "theorem", "toChiralSuperchargeClosure_oddOddClosure"))

    def test_supermetriplectic_chiral_bridge_builds(self) -> None:
        env = os.environ.copy()
        env["PATH"] = f"{Path.home() / '.elan' / 'bin'}:{env['PATH']}"
        cmd = [
            "python3",
            "tools/infra/run_locked_lake_build.py",
            "--wait-for-build-lock",
            "InfoGeometry.SuperMetriplectic.ChiralBridge",
        ]
        subprocess.run(cmd, cwd=REPO, env=env, check=True)


if __name__ == "__main__":
    unittest.main()
