from pathlib import Path
import os
import re
import subprocess
import unittest


REPO = Path(__file__).resolve().parents[1]
CANONICAL = REPO / "lean" / "InfoGeometry" / "Canonical"
TARGET = CANONICAL / "ProjectorNoncommutativityDilationClosure.lean"
ALL = CANONICAL / "All.lean"


def has_decl(text: str, kind: str, name: str) -> bool:
    return re.search(rf"\b{kind}\s+{re.escape(name)}\b", text) is not None


class ProjectorNoncommutativityDilationClosureTests(unittest.TestCase):
    def test_owner_packet_surfaces_exist_and_are_witness_carrying(self) -> None:
        text = TARGET.read_text()
        for name in [
            "DrazinMPProjectorCommutator",
            "ProjectorMismatchAnomaly",
            "DilationFromProjectorNoncommutativity",
            "ConformalClosureWitness",
            "Cl44ConformalReadout",
            "ProjectorNoncommutativityDilationClosurePacket",
        ]:
            self.assertTrue(has_decl(text, "structure", name), name)

        for name in [
            "commutator_eq_projector_obstruction",
            "anomaly_eq_commutator",
            "noncommutativity_requires_dilation_witness",
            "dilation_isGZero",
            "closure_satisfiesKKT_TKK_Weyl_JordanLieClosure",
            "cl44_dilation_isGZero",
        ]:
            self.assertTrue(has_decl(text, "theorem", name), name)

    def test_module_uses_existing_owner_fields_not_unconditional_physics(self) -> None:
        text = TARGET.read_text()
        self.assertIn("ConformalInference", text)
        self.assertIn("SplitCl44TKKJordanLiePacket", text)
        self.assertIn("projectorObstruction", text)
        self.assertIn("DGenerator", text)
        self.assertIn("proof-carrying", text)
        forbidden = [
            "quantum_anomaly_generates_conformal_gravity",
            "proved_CL44_conformal_group",
            "ConformalGravityTheorem",
            "Spin44ClosureTheorem",
            "universeExpansionFromProjectorCommutator",
        ]
        for name in forbidden:
            self.assertNotIn(name, text)

    def test_canonical_all_imports_projector_noncommutativity_closure(self) -> None:
        text = ALL.read_text()
        self.assertIn("import InfoGeometry.Canonical.ProjectorNoncommutativityDilationClosure", text)

    def test_projector_noncommutativity_dilation_closure_builds_locked(self) -> None:
        env = os.environ.copy()
        env.setdefault("PYTHONUNBUFFERED", "1")
        result = subprocess.run(
            [
                "python3",
                "tools/infra/run_locked_lake_build.py",
                "--wait-for-build-lock",
                "InfoGeometry.Canonical.ProjectorNoncommutativityDilationClosure",
            ],
            cwd=REPO,
            env=env,
            text=True,
            stdout=subprocess.PIPE,
            stderr=subprocess.STDOUT,
            timeout=240,
        )
        self.assertEqual(result.returncode, 0, result.stdout)
        self.assertIn("Build completed successfully", result.stdout)


if __name__ == "__main__":
    unittest.main()
