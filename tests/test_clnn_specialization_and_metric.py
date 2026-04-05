import subprocess
import tempfile
import textwrap
import unittest
from pathlib import Path


REPO_ROOT = Path(__file__).resolve().parents[1]


def _run_snippet(body: str) -> subprocess.CompletedProcess[str]:
    with tempfile.TemporaryDirectory(prefix="clnn-specialization-metric-test-") as td:
        path = Path(td) / "ClNNSpecializationAndMetricSmoke.lean"
        path.write_text(
            textwrap.dedent(
                f"""\
                import InfoGeometry.Clifford.ClNNSpecialization
                import InfoGeometry.Clifford.GeneralizedMetricBField

                open InfoGeometry.Clifford.ClNN
                open InfoGeometry.Clifford.ClNNSpecialization
                open InfoGeometry.Clifford.GeneralizedMetricBField

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


class ClNNSpecializationAndMetricTests(unittest.TestCase):
    def test_rank_one_specialization_and_split_metric_surface_theorems_remain_available(self):
        proc = _run_snippet(
            """
            namespace Scratch.ClNNSpecializationAndMetric

            section

            example (x : ℝ × ℝ) :
                rankOneProjection (rankOneSection x) = x := by
              simpa using rankOneProjection_section x

            example (u : Carrier 1) :
                rankOneSection (rankOneProjection u) = u := by
              simpa using rankOneSection_projection u

            example (x : ℝ × ℝ) :
                Quad 1 ((rankOneEquiv).symm x) = InfoGeometry.Clifford.splitQ11 x := by
              simpa using quad_rankOneEquiv_symm x

            example :
                Quad 1 (headNullMinus 0) = 0 := by
              simpa using quad_rankOne_headNullMinus

            example :
                Quad 1 (headNullPlus 0) = 0 := by
              simpa using quad_rankOne_headNullPlus

            variable {n : ℕ}
            variable (G : SplitGeneralizedMetricSeed n)

            example :
                G.plusProjector * G.plusProjector = G.plusProjector := by
              simpa using SplitGeneralizedMetricSeed.plusProjector_idempotent (G := G)

            example :
                G.minusProjector * G.minusProjector = G.minusProjector := by
              simpa using SplitGeneralizedMetricSeed.minusProjector_idempotent (G := G)

            example :
                G.plusProjector + G.minusProjector = 1 := by
              simpa using SplitGeneralizedMetricSeed.plusProjector_add_minusProjector (G := G)

            example :
                G.plusProjector * G.minusProjector = 0 := by
              simpa using SplitGeneralizedMetricSeed.plusProjector_mul_minusProjector (G := G)

            example :
                G.minusProjector * G.plusProjector = 0 := by
              simpa using SplitGeneralizedMetricSeed.minusProjector_mul_plusProjector (G := G)

            example :
                G.polarization * G.plusProjector = G.plusProjector := by
              simpa using SplitGeneralizedMetricSeed.polarization_mul_plusProjector (G := G)

            example :
                G.metricOperator * G.metricOperator = -1 := by
              simpa using SplitGeneralizedMetricSeed.metric_sq_eq_neg_one (G := G)

            end

            end Scratch.ClNNSpecializationAndMetric
            """
        )
        output = _combined_output(proc)
        self.assertEqual(proc.returncode, 0, msg=output)


if __name__ == "__main__":
    unittest.main()
