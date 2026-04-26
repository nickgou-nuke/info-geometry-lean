from pathlib import Path
import os
import re
import subprocess
import unittest


REPO = Path(__file__).resolve().parents[1]
CANONICAL = REPO / "lean" / "InfoGeometry" / "Canonical"
ALL = CANONICAL / "All.lean"

MODULES = [
    "OperatorProjectorMismatch",
    "NormalSemisimpleAgreement",
    "DrazinPenroseAnomalyOwner",
    "DilationKKTBridge",
    "ChiralKMSOwner",
    "WeylSupertraceOwner",
    "ConformalProjectorAgreement",
    "EntanglementResidualOwner",
    "Cl44BridgeCandidate",
]


def has_decl(text: str, kind: str, name: str) -> bool:
    return re.search(rf"\b{kind}\s+{re.escape(name)}\b", text) is not None


class OperatorOwnerMapV2Tests(unittest.TestCase):
    def test_requested_obstruction_first_modules_exist(self) -> None:
        for module in MODULES:
            path = CANONICAL / f"{module}.lean"
            self.assertTrue(path.exists(), module)
            self.assertIn(f"InfoGeometry.Canonical.{module}", ALL.read_text())

    def test_projector_mismatch_core_theorems_are_green_and_one_way(self) -> None:
        text = (CANONICAL / "OperatorProjectorMismatch.lean").read_text()
        for name in [
            "ProjectorPair",
            "DrazinMPProjectorData",
            "ProjectorCommutatorObstruction",
        ]:
            self.assertTrue(has_decl(text, "structure", name), name)
        for name in [
            "projectorAgreement_iff_eq",
            "projectorAgreement_implies_commutator_eq_zero",
            "commutator_ne_zero_implies_mismatch_ne_zero",
            "hasProjectorAnomaly_iff_hasMismatch",
        ]:
            self.assertTrue(has_decl(text, "theorem", name), name)
        forbidden = [
            "mismatch_ne_zero_implies_commutator_ne_zero",
            "commutator_zero_implies_agreement",
            "every_projector_mismatch_admits_dilation",
            "projector_commutator_implies_conformal_gravity",
        ]
        for name in forbidden:
            self.assertNotIn(name, text)

    def test_conformal_projector_agreement_marks_mp_metric_tear_point(self) -> None:
        text = (CANONICAL / "ConformalProjectorAgreement.lean").read_text()
        for name in [
            "DrazinSimilarityTransportWitness",
            "MoorePenroseMetricTransportWitness",
            "ConformalMismatchTransportWitness",
        ]:
            self.assertTrue(has_decl(text, "structure", name), name)
        self.assertTrue(has_decl(text, "theorem", "drazinProjector_equivariant"))
        self.assertTrue(has_decl(text, "theorem", "moorePenroseProjector_equivariant_of_metricWitness"))
        self.assertIn("metric-natural", text)
        self.assertIn("similarity-natural", text)
        self.assertNotIn("moorePenroseProjector_equivariant_of_arbitrary_similarity", text)

    def test_entanglement_and_cl44_are_witness_only(self) -> None:
        ent = (CANONICAL / "EntanglementResidualOwner.lean").read_text()
        self.assertTrue(has_decl(ent, "structure", "DrazinNullCovariance"))
        self.assertTrue(has_decl(ent, "structure", "EntanglementCriterionWitness"))
        self.assertTrue(has_decl(ent, "theorem", "nonfactorizingCovariance_implies_drazinNullSupportedCorrelation"))
        self.assertIn("not the entanglement itself", ent)
        self.assertNotIn("entanglement_eq_drazin_projector_residue", ent)

        cl44 = (CANONICAL / "Cl44BridgeCandidate.lean").read_text()
        self.assertTrue(has_decl(cl44, "structure", "Cl44BridgeCandidate"))
        for field in [
            "metricTransportWitness",
            "realCliffordRepresentationWitness",
            "nullConePreservationWitness",
            "quantizationWitness",
        ]:
            self.assertIn(field, cl44)
        self.assertIn("candidate bridge", cl44)
        self.assertNotIn("Cl44ClosureTheorem", cl44)
        self.assertNotIn("conformal_gravity_theorem", cl44)

    def test_operator_owner_map_v2_builds_locked(self) -> None:
        env = os.environ.copy()
        env.setdefault("PYTHONUNBUFFERED", "1")
        result = subprocess.run(
            [
                "python3",
                "tools/infra/run_locked_lake_build.py",
                "--wait-for-build-lock",
                "InfoGeometry.Canonical.Cl44BridgeCandidate",
            ],
            cwd=REPO,
            env=env,
            text=True,
            stdout=subprocess.PIPE,
            stderr=subprocess.STDOUT,
            timeout=300,
        )
        self.assertEqual(result.returncode, 0, result.stdout)
        self.assertIn("Build completed successfully", result.stdout)


if __name__ == "__main__":
    unittest.main()
