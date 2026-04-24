from pathlib import Path
import re
import subprocess
import unittest
import os


REPO = Path(__file__).resolve().parents[1]
BRIDGE = REPO / "lean" / "InfoGeometry" / "SuperMetriplectic" / "CartanBridge.lean"


def has_decl(text: str, kind: str, name: str) -> bool:
    if kind == "def":
        pattern = rf"(?m)^\s*(?:noncomputable\s+)?def\s+{re.escape(name)}\b"
    else:
        pattern = rf"(?m)^\s*{kind}\s+{re.escape(name)}\b"
    return re.search(pattern, text) is not None


class SuperMetriplecticCartanBridgeTests(unittest.TestCase):
    def test_bridge_surface_exists(self) -> None:
        self.assertTrue(BRIDGE.exists(), f"missing bridge file: {BRIDGE}")
        text = BRIDGE.read_text()
        self.assertIn("InfoGeometry.SuperMetriplectic.CartanBridge", text)
        self.assertTrue(has_decl(text, "structure", "DrazinCartanOnsagerBridge"))
        self.assertTrue(has_decl(text, "def", "spectralCartanSymmetricLieAlgebra"))
        self.assertTrue(has_decl(text, "def", "toCartanOnsagerSplit"))
        self.assertTrue(has_decl(text, "theorem", "toCartanOnsagerSplit_drazinCore_eq_k"))
        self.assertTrue(has_decl(text, "theorem", "toCartanOnsagerSplit_dissipativeRange_eq_p"))

    def test_supermetriplectic_all_builds_with_cartan_bridge(self) -> None:
        env = os.environ.copy()
        env["PATH"] = f"{Path.home() / '.elan' / 'bin'}:{env['PATH']}"
        cmd = [
            "python3",
            "tools/infra/run_locked_lake_build.py",
            "--wait-for-build-lock",
            "InfoGeometry.SuperMetriplectic.All",
        ]
        subprocess.run(cmd, cwd=REPO, env=env, check=True)


if __name__ == "__main__":
    unittest.main()
