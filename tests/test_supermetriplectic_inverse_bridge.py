from pathlib import Path
import re
import subprocess
import unittest
import os


REPO = Path(__file__).resolve().parents[1]
BRIDGE = REPO / "lean" / "InfoGeometry" / "SuperMetriplectic" / "InverseBridge.lean"


def has_decl(text: str, kind: str, name: str) -> bool:
    if kind == "def":
        pattern = rf"(?m)^\s*(?:noncomputable\s+)?def\s+{re.escape(name)}\b"
    else:
        pattern = rf"(?m)^\s*{kind}\s+{re.escape(name)}\b"
    return re.search(pattern, text) is not None


class SuperMetriplecticInverseBridgeTests(unittest.TestCase):
    def test_bridge_surface_exists(self) -> None:
        self.assertTrue(BRIDGE.exists(), f"missing bridge file: {BRIDGE}")
        text = BRIDGE.read_text()
        self.assertIn("InfoGeometry.SuperMetriplectic.InverseBridge", text)
        self.assertTrue(has_decl(text, "theorem", "toIsMoorePenroseInverse"))
        self.assertTrue(has_decl(text, "theorem", "toIsDrazinInverse"))
        self.assertTrue(has_decl(text, "theorem", "hiddenBlock_hasMoorePenroseShadow"))
        self.assertTrue(has_decl(text, "theorem", "hiddenBlock_hasDrazinShadow"))

    def test_supermetriplectic_inverse_bridge_builds(self) -> None:
        env = os.environ.copy()
        env["PATH"] = f"{Path.home() / '.elan' / 'bin'}:{env['PATH']}"
        cmd = [
            "python3",
            "tools/infra/run_locked_lake_build.py",
            "--wait-for-build-lock",
            "InfoGeometry.SuperMetriplectic.InverseBridge",
        ]
        subprocess.run(cmd, cwd=REPO, env=env, check=True)


if __name__ == "__main__":
    unittest.main()
