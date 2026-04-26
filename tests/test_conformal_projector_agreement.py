from pathlib import Path
import os
import re
import subprocess
import unittest


REPO = Path(__file__).resolve().parents[1]
CANONICAL = REPO / "lean" / "InfoGeometry" / "Canonical"
TARGET = CANONICAL / "ConformalProjectorAgreement.lean"
ALL = CANONICAL / "All.lean"


def has_decl(text: str, kind: str, name: str) -> bool:
    return re.search(rf"\b{kind}\s+{re.escape(name)}\b", text) is not None


class ConformalProjectorAgreementTests(unittest.TestCase):
    def test_phase_c_transport_surfaces_exist(self) -> None:
        text = TARGET.read_text()
        for name in [
            "DrazinSimilarityTransportWitness",
            "MoorePenroseMetricTransportWitness",
            "ConformalMismatchTransportWitness",
        ]:
            self.assertTrue(has_decl(text, "structure", name), name)

        for name in [
            "drazinProjector_equivariant",
            "moorePenroseProjector_equivariant_of_metricWitness",
            "MPFixedMetricTear",
            "mismatch_fixedMetric_decomposition",
            "moorePenrose_not_generic_similarity_equivariant_under_fixed_metric",
        ]:
            self.assertTrue(has_decl(text, "theorem", name) or has_decl(text, "def", name), name)

    def test_phase_c_boundaries_are_theorem_safe(self) -> None:
        text = TARGET.read_text()
        self.assertIn("similarity-natural", text)
        self.assertIn("metric-natural", text)
        self.assertNotIn("moorePenroseProjector_equivariant_of_arbitrary_similarity", text)
        self.assertNotIn("ConformalGravityTheorem", text)

    def test_canonical_all_imports_conformal_projector_agreement(self) -> None:
        text = ALL.read_text()
        self.assertIn("import InfoGeometry.Canonical.ConformalProjectorAgreement", text)

    def test_conformal_projector_agreement_builds_locked(self) -> None:
        env = os.environ.copy()
        env.setdefault("PYTHONUNBUFFERED", "1")
        result = subprocess.run(
            [
                "python3",
                "tools/infra/run_locked_lake_build.py",
                "--wait-for-build-lock",
                "InfoGeometry.Canonical.ConformalProjectorAgreement",
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
