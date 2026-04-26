from pathlib import Path
import os
import re
import subprocess
import unittest


REPO = Path(__file__).resolve().parents[1]
CANONICAL = REPO / "lean" / "InfoGeometry" / "Canonical"
TARGET = CANONICAL / "MetricTransportWitness.lean"
CLOSURE = CANONICAL / "ProjectorNoncommutativityDilationClosure.lean"


def has_decl(text: str, kind: str, name: str) -> bool:
    return re.search(rf"\b{kind}\s+{re.escape(name)}\b", text) is not None


class MetricTransportWitnessTests(unittest.TestCase):
    def test_owner_surfaces_exist(self) -> None:
        text = TARGET.read_text()
        for name in [
            "MetricAdjointData",
            "MoorePenroseInverseG",
            "SimilarityTransportWitness",
            "MetricCompensatorWitness",
            "LocalGaugeMetricTransportWitness",
        ]:
            self.assertTrue(has_decl(text, "structure", name), name)

        for name in [
            "MPFixedTear",
            "mismatch_G",
        ]:
            self.assertTrue(has_decl(text, "def", name), name)

        for name in [
            "transported_metric_restores_mp_covariance",
            "mismatch_transport_decomposition",
            "transported_mismatch_covariant",
        ]:
            self.assertTrue(has_decl(text, "theorem", name), name)

    def test_no_automatic_gravity_closure_claim(self) -> None:
        text = TARGET.read_text()
        forbidden = [
            "projector_mismatch_implies_conformal_gravity",
            "all_forces_are_projector_commutators",
            "metric_transport_deletes_anomaly",
            "automatic_cl44_closure",
        ]
        for token in forbidden:
            self.assertNotIn(token, text)

    def test_closure_module_imports_metric_transport_layer(self) -> None:
        text = CLOSURE.read_text()
        self.assertIn("import InfoGeometry.Canonical.MetricTransportWitness", text)

    def test_metric_transport_module_builds_locked(self) -> None:
        env = os.environ.copy()
        env.setdefault("PYTHONUNBUFFERED", "1")
        result = subprocess.run(
            [
                "python3",
                "tools/infra/run_locked_lake_build.py",
                "--wait-for-build-lock",
                "InfoGeometry.Canonical.MetricTransportWitness",
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
