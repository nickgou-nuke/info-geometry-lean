from pathlib import Path
import re
import subprocess
import unittest
import os


REPO = Path(__file__).resolve().parents[1]
BRIDGE = REPO / "lean" / "InfoGeometry" / "SuperMetriplectic" / "EntropyShadowBridge.lean"


def has_decl(text: str, kind: str, name: str) -> bool:
    if kind == "def":
        pattern = rf"(?m)^\s*(?:noncomputable\s+)?def\s+{re.escape(name)}\b"
    else:
        pattern = rf"(?m)^\s*{kind}\s+{re.escape(name)}\b"
    return re.search(pattern, text) is not None


class SuperMetriplecticEntropyShadowBridgeTests(unittest.TestCase):
    def test_bridge_surface_exists(self) -> None:
        self.assertTrue(BRIDGE.exists(), f"missing bridge file: {BRIDGE}")
        text = BRIDGE.read_text()
        self.assertIn("InfoGeometry.SuperMetriplectic.EntropyShadowBridge", text)
        self.assertTrue(has_decl(text, "theorem", "hiddenBlock_projectorMismatch_eq_zero_iff"))
        self.assertTrue(has_decl(text, "theorem", "hiddenBlock_chiralAnomaly_eq_zero_of_projectorMismatch_eq_zero"))
        self.assertTrue(has_decl(text, "def", "toCoadjointLeafEntropySplit"))
        self.assertTrue(has_decl(text, "theorem", "toCoadjointLeafEntropySplit_totalEntropyChange_eq_entropyProduction"))

    def test_entropy_shadow_bridge_builds(self) -> None:
        env = os.environ.copy()
        env["PATH"] = f"{Path.home() / '.elan' / 'bin'}:{env['PATH']}"
        cmd = [
            "python3",
            "tools/infra/run_locked_lake_build.py",
            "--wait-for-build-lock",
            "InfoGeometry.SuperMetriplectic.EntropyShadowBridge",
        ]
        subprocess.run(cmd, cwd=REPO, env=env, check=True)


if __name__ == "__main__":
    unittest.main()
