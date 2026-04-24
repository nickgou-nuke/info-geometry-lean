from pathlib import Path
import re
import subprocess
import unittest
import os


REPO = Path(__file__).resolve().parents[1]
BRIDGE = REPO / "lean" / "InfoGeometry" / "SuperMetriplectic" / "DrazinBridge.lean"
ALL = REPO / "lean" / "InfoGeometry" / "SuperMetriplectic" / "All.lean"


def has_decl(text: str, kind: str, name: str) -> bool:
    if kind == "def":
        pattern = rf"(?m)^\s*(?:noncomputable\s+)?def\s+{re.escape(name)}\b"
    else:
        pattern = rf"(?m)^\s*{kind}\s+{re.escape(name)}\b"
    return re.search(pattern, text) is not None


class SuperMetriplecticDrazinBridgeTests(unittest.TestCase):
    def test_bridge_surface_exists(self) -> None:
        bridge_text = BRIDGE.read_text(encoding="utf-8")
        all_text = ALL.read_text(encoding="utf-8")

        self.assertIn("import InfoGeometry.SuperMetriplectic.DrazinBridge", all_text)
        self.assertTrue(has_decl(bridge_text, "structure", "DrazinSuperchargeClosureBridge"))
        self.assertTrue(has_decl(bridge_text, "def", "toSuperchargeClosure"))
        self.assertTrue(has_decl(bridge_text, "theorem", "toSuperchargeClosure_translationShadow_eq_drazinTranslationCandidate"))
        self.assertTrue(has_decl(bridge_text, "theorem", "toSuperchargeClosure_defectShadow_eq_drazinCentralCandidate"))
        self.assertTrue(has_decl(bridge_text, "theorem", "toSuperchargeClosure_oddOddClosure"))

    def test_supermetriplectic_all_builds(self) -> None:
        proc = subprocess.run(
            [
                "python3",
                "tools/infra/run_locked_lake_build.py",
                "--wait-for-build-lock",
                "InfoGeometry.SuperMetriplectic.All",
            ],
            cwd=REPO,
            text=True,
            capture_output=True,
            env={**os.environ, "PATH": f"{Path.home() / '.elan' / 'bin'}:{os.environ.get('PATH', '')}"},
        )
        output = f"{proc.stdout}\n{proc.stderr}"
        self.assertEqual(proc.returncode, 0, msg=output)


if __name__ == "__main__":
    unittest.main()
