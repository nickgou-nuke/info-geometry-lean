from pathlib import Path
import re
import subprocess
import unittest
import os


REPO = Path(__file__).resolve().parents[1]
BRIDGE = REPO / "lean" / "InfoGeometry" / "SuperMetriplectic" / "TriadBridge.lean"
ALL = REPO / "lean" / "InfoGeometry" / "SuperMetriplectic" / "All.lean"


def has_decl(text: str, kind: str, name: str) -> bool:
    if kind == "def":
        pattern = rf"(?m)^\s*(?:noncomputable\s+)?def\s+{re.escape(name)}\b"
    else:
        pattern = rf"(?m)^\s*{kind}\s+{re.escape(name)}\b"
    return re.search(pattern, text) is not None


class SuperMetriplecticTriadBridgeTests(unittest.TestCase):
    def test_bridge_surface_exists(self) -> None:
        bridge_text = BRIDGE.read_text(encoding="utf-8")
        all_text = ALL.read_text(encoding="utf-8")

        self.assertIn("import InfoGeometry.SuperMetriplectic.TriadBridge", all_text)
        self.assertTrue(has_decl(bridge_text, "structure", "TriadCompatibleOddPacket"))
        self.assertTrue(has_decl(bridge_text, "def", "toChiralSuperchargeClosure"))
        self.assertTrue(has_decl(bridge_text, "theorem", "toChiralSuperchargeClosure_translationShadow_eq_effectiveEvenOnsager"))
        self.assertTrue(has_decl(bridge_text, "theorem", "toChiralSuperchargeClosure_defectShadow_eq_drazinDefectProjector"))
        self.assertTrue(has_decl(bridge_text, "structure", "DrazinPenroseSchurChiralTriadBridge"))
        self.assertTrue(has_decl(bridge_text, "def", "chiralClosureOfTriadOddData"))
        self.assertTrue(has_decl(bridge_text, "theorem", "chiralClosureOfTriadOddData_translationShadow_eq_effectiveEvenOnsager"))
        self.assertTrue(has_decl(bridge_text, "theorem", "chiralClosureOfTriadOddData_defectShadow_eq_drazinDefectProjector"))
        self.assertTrue(has_decl(bridge_text, "theorem", "toChiralSuperchargeClosure_eq_chiralClosureOfTriadOddData"))
        self.assertTrue(has_decl(bridge_text, "def", "ofTriadCompatibleOddPacket"))
        self.assertTrue(has_decl(bridge_text, "def", "ofTriadOddData"))
        self.assertTrue(has_decl(bridge_text, "theorem", "ofTriadOddData_eq_ofTriadCompatibleOddPacket"))
        self.assertTrue(has_decl(bridge_text, "def", "hiddenBlockChiralAnomaly"))
        self.assertTrue(has_decl(bridge_text, "def", "toChiralSuperchargeClosure"))
        self.assertTrue(has_decl(bridge_text, "theorem", "hiddenBlock_hasMoorePenroseShadow"))
        self.assertTrue(has_decl(bridge_text, "theorem", "hiddenBlock_hasDrazinShadow"))
        self.assertTrue(has_decl(bridge_text, "theorem", "hiddenBlock_chiralAnomaly_eq_zero_of_projectorMismatch_eq_zero"))
        self.assertTrue(has_decl(bridge_text, "def", "toCoadjointLeafEntropySplit"))
        self.assertTrue(has_decl(bridge_text, "theorem", "toCoadjointLeafEntropySplit_totalEntropyChange_eq_entropyProduction"))
        self.assertTrue(has_decl(bridge_text, "theorem", "effective_metric_is_schur_complement"))

    def test_supermetriplectic_triad_bridge_builds(self) -> None:
        env = os.environ.copy()
        env["PATH"] = f"{Path.home() / '.elan' / 'bin'}:{env['PATH']}"
        cmd = [
            "python3",
            "tools/infra/run_locked_lake_build.py",
            "--wait-for-build-lock",
            "InfoGeometry.SuperMetriplectic.TriadBridge",
        ]
        subprocess.run(cmd, cwd=REPO, env=env, check=True)


if __name__ == "__main__":
    unittest.main()
