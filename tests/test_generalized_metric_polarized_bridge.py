import subprocess
import tempfile
import textwrap
import unittest
from pathlib import Path


REPO_ROOT = Path(__file__).resolve().parents[1]


def _run_snippet(body: str) -> subprocess.CompletedProcess[str]:
    with tempfile.TemporaryDirectory(prefix="generalized-metric-polarized-bridge-test-") as td:
        path = Path(td) / "GeneralizedMetricPolarizedBridgeSmoke.lean"
        path.write_text(
            textwrap.dedent(
                f"""\
                import InfoGeometry.Canonical.GeneralizedMetricPolarizedBridge

                open scoped InnerProductSpace
                open InfoGeometry.Canonical.GeneralizedMetricCore
                open InfoGeometry.Canonical.GeneralizedMetricPolarizedBridge
                open InfoGeometry.Canonical.RelativeModularPolarizedBridge
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


class GeneralizedMetricPolarizedBridgeTests(unittest.TestCase):
    def test_generalized_metric_polarized_bridge_surface_theorems_remain_available(self):
        proc = _run_snippet(
            """
            namespace Scratch.GeneralizedMetricPolarizedBridge

            section

            variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
            variable {α : Type*} [Fintype α] [Nonempty α]
            variable {βplus : Type*} [Fintype βplus] [Nonempty βplus]
            variable {βminus : Type*} [Fintype βminus] [Nonempty βminus]

            local notation "H2" => InfoGeometry.Krein.DoubledSpace H

            variable (u : H2)
            variable (huplus : u ∈ plusSheet (E := H))
            variable (huminus : u ∈ minusSheet (E := H))
            variable (R : PolarizedRelativeModularPair H α βplus βminus)
            variable (bplus : βplus) (bminus : βminus)

            example :
                GeneralizedMetricSeed.plusProjector (tomitaGeneralizedMetricSeed : GeneralizedMetricSeed H) u = u := by
              simpa using
                tomitaGeneralizedMetricSeed_plusProjector_eq_self_of_mem_plusSheet
                  (H := H) (u := u) huplus

            example :
                GeneralizedMetricSeed.minusProjector (tomitaGeneralizedMetricSeed : GeneralizedMetricSeed H) u = u := by
              simpa using
                tomitaGeneralizedMetricSeed_minusProjector_eq_self_of_mem_minusSheet
                  (H := H) (u := u) huminus

            example :
                GeneralizedMetricSeed.plusProjector (tomitaGeneralizedMetricSeed : GeneralizedMetricSeed H)
                  (R.plus.lift bplus) = R.plus.lift bplus := by
              simpa using
                PolarizedRelativeModularPair.plus_lift_fixed_by_tomitaGeneralizedMetric
                  (R := R) (b := bplus)

            example :
                GeneralizedMetricSeed.minusProjector (tomitaGeneralizedMetricSeed : GeneralizedMetricSeed H)
                  (R.minus.lift bminus) = R.minus.lift bminus := by
              simpa using
                PolarizedRelativeModularPair.minus_lift_fixed_by_tomitaGeneralizedMetric
                  (R := R) (b := bminus)

            example :
                (PolarizedRelativeModularPair.toGeneralizedMetricWitness (R := R)).polarized = R := by
              rfl

            end

            end Scratch.GeneralizedMetricPolarizedBridge
            """
        )
        output = _combined_output(proc)
        self.assertEqual(proc.returncode, 0, msg=output)


if __name__ == "__main__":
    unittest.main()
