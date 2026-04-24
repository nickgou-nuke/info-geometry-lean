from pathlib import Path
import re
import subprocess
import unittest
import os


REPO = Path(__file__).resolve().parents[1]
BRIDGE = REPO / "lean" / "InfoGeometry" / "SuperMetriplectic" / "DrazinProjectorConstraintBridge.lean"
ALL = REPO / "lean" / "InfoGeometry" / "SuperMetriplectic" / "All.lean"


def has_decl(text: str, kind: str, name: str) -> bool:
    if kind == "def":
        pattern = rf"(?m)^\s*(?:noncomputable\s+)?def\s+{re.escape(name)}\b"
    else:
        pattern = rf"(?m)^\s*{kind}\s+{re.escape(name)}\b"
    return re.search(pattern, text) is not None


class SuperMetriplecticDrazinProjectorConstraintBridgeTests(unittest.TestCase):
    def test_bridge_surface_exists(self) -> None:
        bridge_text = BRIDGE.read_text(encoding="utf-8")
        all_text = ALL.read_text(encoding="utf-8")

        self.assertIn("import InfoGeometry.SuperMetriplectic.DrazinProjectorConstraintBridge", all_text)
        self.assertTrue(has_decl(bridge_text, "structure", "DrazinProjectorConstraintCompatibility"))
        self.assertTrue(has_decl(bridge_text, "def", "topologicalConstraintProjector"))
        self.assertTrue(has_decl(bridge_text, "def", "topologicalConstraintReadout"))
        self.assertTrue(has_decl(bridge_text, "theorem", "topologicalConstraintReadout_eq_topologicalConstraintProjector"))
        self.assertTrue(has_decl(bridge_text, "theorem", "topologicalConstraintProjector_readout_eq_drazin_formula"))
        self.assertTrue(has_decl(bridge_text, "theorem", "scalar_readout_seal"))

    def test_supermetriplectic_drazin_projector_constraint_bridge_builds(self) -> None:
        env = os.environ.copy()
        env["PATH"] = f"{Path.home() / '.elan' / 'bin'}:{env['PATH']}"
        cmd = [
            "python3",
            "tools/infra/run_locked_lake_build.py",
            "--wait-for-build-lock",
            "InfoGeometry.SuperMetriplectic.DrazinProjectorConstraintBridge",
        ]
        subprocess.run(cmd, cwd=REPO, env=env, check=True)


if __name__ == "__main__":
    unittest.main()
