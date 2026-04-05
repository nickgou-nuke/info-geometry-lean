import subprocess
import tempfile
import textwrap
import unittest
from pathlib import Path


REPO_ROOT = Path(__file__).resolve().parents[1]


def _run_snippet(body: str) -> subprocess.CompletedProcess[str]:
    with tempfile.TemporaryDirectory(prefix="generalized-metric-recomposition-bridge-test-") as td:
        path = Path(td) / "GeneralizedMetricRecompositionBridgeSmoke.lean"
        path.write_text(
            textwrap.dedent(
                f"""\
                import InfoGeometry.Canonical.GeneralizedMetricRecompositionBridge

                open scoped InnerProductSpace
                open InfoGeometry.Canonical.RelativeModularRecomposition
                open InfoGeometry.Canonical.GeneralizedMetricRecompositionBridge
                open InfoGeometry.Krein.SplitQuadraticSheets

                {body}
                """
            ),
            encoding="utf-8",
        )
        return subprocess.run(
            ["lake", "env", "lean", str(path)],
            cwd=REPO_ROOT,
            text=True,
            capture_output=True,
        )


def _combined_output(proc: subprocess.CompletedProcess[str]) -> str:
    return f"{proc.stdout}\n{proc.stderr}"


class GeneralizedMetricRecompositionBridgeTests(unittest.TestCase):
    def test_generalized_metric_recomposition_bridge_surfaces_remain_available(self):
        proc = _run_snippet(
            """
            namespace Scratch.GeneralizedMetricRecompositionBridge

            section

            variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
            variable {α : Type*} [Fintype α] [Nonempty α]
            variable {βplus : Type*} [Fintype βplus] [Nonempty βplus]
            variable {βminus : Type*} [Fintype βminus] [Nonempty βminus]
            variable (R : PolarizedRecompositionData H α βplus βminus)
            variable (bplus : βplus) (bminus : βminus)

            example :
                PolarizedRecompositionData.plusMetricTransportLift R bplus ∈ minusSheet (E := H) := by
              simpa using
                PolarizedRecompositionData.plusMetricTransportLift_mem_minusSheet
                  (R := R) (b := bplus)

            example :
                PolarizedRecompositionData.minusMetricTransportLift R bminus ∈ plusSheet (E := H) := by
              simpa using
                PolarizedRecompositionData.minusMetricTransportLift_mem_plusSheet
                  (R := R) (b := bminus)

            example :
                PolarizedRecompositionData.generalizedMetricTwistShadow R = R.couplingLogDefect := by
              simpa using
                PolarizedRecompositionData.generalizedMetricTwistShadow_eq_couplingLogDefect
                  (R := R)

            example :
                PolarizedRecompositionData.generalizedMetricPotentialShadow R = R.couplingPotentialDefect := by
              simpa using
                PolarizedRecompositionData.generalizedMetricPotentialShadow_eq_couplingPotentialDefect
                  (R := R)

            example :
                R.recomposedLogDensity bplus bminus
                  = R.recomposedCommonCarrierLogDensity bplus bminus
                      + PolarizedRecompositionData.generalizedMetricTwistShadow R := by
              simpa using
                PolarizedRecompositionData.recomposedLogDensity_eq_commonCarrier_add_generalizedMetricTwistShadow
                  (R := R) (bplus := bplus) (bminus := bminus)

            example :
                R.recomposedModularPotential bplus bminus
                  = R.recomposedCommonCarrierModularPotential bplus bminus
                      + PolarizedRecompositionData.generalizedMetricPotentialShadow R := by
              simpa using
                PolarizedRecompositionData.recomposedModularPotential_eq_commonCarrier_add_generalizedMetricPotentialShadow
                  (R := R) (bplus := bplus) (bminus := bminus)

            example :
                PolarizedRecompositionData.generalizedMetricTwistShadow R = 0 ↔ R.exactLogRecomposition := by
              simpa using
                PolarizedRecompositionData.generalizedMetricTwistShadow_eq_zero_iff_exactLogRecomposition
                  (R := R)

            example :
                PolarizedRecompositionData.generalizedMetricPotentialShadow R = 0 ↔ R.exactPotentialRecomposition := by
              simpa using
                PolarizedRecompositionData.generalizedMetricPotentialShadow_eq_zero_iff_exactPotentialRecomposition
                  (R := R)

            end

            end Scratch.GeneralizedMetricRecompositionBridge
            """
        )
        output = _combined_output(proc)
        self.assertEqual(proc.returncode, 0, msg=output)


if __name__ == "__main__":
    unittest.main()
