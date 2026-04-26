from pathlib import Path
import re
import unittest

REPO = Path(__file__).resolve().parents[1]
CANONICAL = REPO / "lean" / "InfoGeometry" / "Canonical"


def has_decl(text: str, kind: str, name: str) -> bool:
    return re.search(rf"\b{kind}\s+{re.escape(name)}\b", text) is not None


class ProjectorAnomalyTransportSyncV2Tests(unittest.TestCase):
    def test_phase_b_is_pure_projector_algebra(self) -> None:
        text = (CANONICAL / "OperatorProjectorMismatch.lean").read_text()
        for name in [
            "ProjectorMismatch",
            "ProjectorCommutator",
            "SpectralMetricMismatch",
            "NoncommutingSplit",
            "projectorMismatch_eq_zero_iff_projectors_eq",
            "projectorMismatch_eq_zero_implies_projectorCommutator_eq_zero",
            "projectorCommutator_ne_zero_implies_projectorMismatch_ne_zero",
        ]:
            self.assertIn(name, text, name)
        forbidden = [
            "dilation", "gravity", "conformal closure", "Cl(4,4)",
            "projectorMismatch_ne_zero_implies_projectorCommutator_ne_zero",
        ]
        lowered = text.lower()
        for phrase in forbidden[:3]:
            self.assertNotIn(phrase, lowered)
        for name in forbidden[3:]:
            self.assertNotIn(name, text)

    def test_phase_c_has_sufficient_metric_transport_and_counterexample_not_iff(self) -> None:
        text = (CANONICAL / "ConformalProjectorAgreement.lean").read_text()
        for name in [
            "MetricTransportWitness",
            "MPFixedTear",
            "MismatchG",
            "fixedMetric_mismatch_decomposition",
            "transportedMetric_mismatch_covariance",
            "moorePenroseProjector_equivariant_of_G_isometry",
            "shearCounterexample_Aprime_eq",
            "shearCounterexample_drazin_ne_euclideanMP",
            "shearCounterexample_fixedMetric_MP_transport_fails",
        ]:
            self.assertIn(name, text, name)
        forbidden = [
            "iff_metric_transport",
            "metric_transport_iff",
            "moorePenroseProjector_equivariant_iff",
            "G_transported_unique",
        ]
        for name in forbidden:
            self.assertNotIn(name, text)

    def test_phase_a_removes_dilation_necessity_and_keeps_cl44_witness_only(self) -> None:
        text = (CANONICAL / "ProjectorNoncommutativityDilationClosure.lean").read_text()
        for name in [
            "HasProjectorAnomaly",
            "HasNoncommutingProjectorObstruction",
            "noncommuting_obstruction_implies_projector_anomaly",
            "DilationClosureWitness",
            "ConformalClosureWitness",
            "Cl44ConformalReadout",
            "ProjectorToCl44BridgeCandidate",
        ]:
            self.assertIn(name, text, name)
        forbidden = [
            "necessary algebraic completion",
            "commutator_implies_dilationGenerator_exists",
            "ProjectorCommutator_ne_zero_implies_dilation",
            "quantum anomaly generates conformal gravity",
            "Cl44ClosureTheorem",
        ]
        for phrase in forbidden:
            self.assertNotIn(phrase, text)


if __name__ == "__main__":
    unittest.main()
