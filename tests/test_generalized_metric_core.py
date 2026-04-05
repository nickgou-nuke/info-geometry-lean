import subprocess
import tempfile
import textwrap
import unittest
from pathlib import Path


REPO_ROOT = Path(__file__).resolve().parents[1]


def _run_snippet(body: str) -> subprocess.CompletedProcess[str]:
    with tempfile.TemporaryDirectory(prefix="generalized-metric-core-test-") as td:
        path = Path(td) / "GeneralizedMetricCoreSmoke.lean"
        path.write_text(
            textwrap.dedent(
                f"""\
                import InfoGeometry.Canonical.GeneralizedMetricCore

                open scoped InnerProductSpace
                open InfoGeometry.Canonical.GeneralizedMetricCore
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


class GeneralizedMetricCoreTests(unittest.TestCase):
    def test_generalized_metric_core_surface_theorems_remain_available(self):
        proc = _run_snippet(
            """
            namespace Scratch.GeneralizedMetricCore

            section

            variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
            local notation "H2" => InfoGeometry.Krein.DoubledSpace H
            local notation "EndH" => H2 →L[ℝ] H2
            local notation "IdH" => ContinuousLinearMap.id ℝ H2

            variable (G : GeneralizedMetricSeed H)
            variable (u : H2)

            example :
                (GeneralizedMetricSeed.plusProjector G).comp (GeneralizedMetricSeed.plusProjector G)
                  = GeneralizedMetricSeed.plusProjector G := by
              simpa using GeneralizedMetricSeed.plusProjector_idempotent (G := G)

            example :
                (GeneralizedMetricSeed.minusProjector G).comp (GeneralizedMetricSeed.minusProjector G)
                  = GeneralizedMetricSeed.minusProjector G := by
              simpa using GeneralizedMetricSeed.minusProjector_idempotent (G := G)

            example :
                GeneralizedMetricSeed.plusProjector G + GeneralizedMetricSeed.minusProjector G = IdH := by
              simpa using GeneralizedMetricSeed.plusProjector_add_minusProjector (G := G)

            example :
                (GeneralizedMetricSeed.plusProjector G).comp (GeneralizedMetricSeed.minusProjector G) = 0 := by
              simpa using GeneralizedMetricSeed.plusProjector_comp_minusProjector (G := G)

            example :
                G.metricOperator.comp G.metricOperator = -IdH := by
              simpa using GeneralizedMetricSeed.metric_sq_eq_neg_id (G := G)

            example :
                (G.metricOperator.comp G.eta).comp G.metricOperator = G.eta := by
              simpa using GeneralizedMetricSeed.metric_conjugates_eta (G := G)

            example :
                u = GeneralizedMetricSeed.plusProjector G u + GeneralizedMetricSeed.minusProjector G u := by
              simpa using GeneralizedMetricSeed.decompose (G := G) (u := u)

            example :
                (tomitaGeneralizedMetricSeed : GeneralizedMetricSeed H).metricOperator
                  = InfoGeometry.Krein.dilationOperator (E := H) := by
              simpa using tomitaGeneralizedMetricSeed_metricOperator_eq_dilationOperator (H := H)

            example :
                GeneralizedMetricSeed.plusProjector (tomitaGeneralizedMetricSeed : GeneralizedMetricSeed H)
                  = InfoGeometry.Krein.spectralPlusProj (E := H) := by
              simpa using tomitaGeneralizedMetricSeed_plusProjector_eq_spectralPlusProj (H := H)

            example :
                GeneralizedMetricSeed.minusProjector (tomitaGeneralizedMetricSeed : GeneralizedMetricSeed H)
                  = InfoGeometry.Krein.spectralMinusProj (E := H) := by
              simpa using tomitaGeneralizedMetricSeed_minusProjector_eq_spectralMinusProj (H := H)

            example :
                GeneralizedMetricSeed.plusProjector (tomitaGeneralizedMetricSeed : GeneralizedMetricSeed H) u
                  ∈ plusSheet (E := H) := by
              simpa using tomitaGeneralizedMetricSeed_plusProjector_mem_plusSheet (H := H) u

            example :
                GeneralizedMetricSeed.minusProjector (tomitaGeneralizedMetricSeed : GeneralizedMetricSeed H) u
                  ∈ minusSheet (E := H) := by
              simpa using tomitaGeneralizedMetricSeed_minusProjector_mem_minusSheet (H := H) u

            example :
                u
                  = GeneralizedMetricSeed.plusProjector (tomitaGeneralizedMetricSeed : GeneralizedMetricSeed H) u
                    + GeneralizedMetricSeed.minusProjector (tomitaGeneralizedMetricSeed : GeneralizedMetricSeed H) u := by
              simpa using tomitaGeneralizedMetricSeed_decompose (H := H) u

            end

            end Scratch.GeneralizedMetricCore
            """
        )
        output = _combined_output(proc)
        self.assertEqual(proc.returncode, 0, msg=output)


if __name__ == "__main__":
    unittest.main()
