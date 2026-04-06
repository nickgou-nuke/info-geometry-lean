import subprocess
import tempfile
import textwrap
import unittest
from pathlib import Path


REPO_ROOT = Path(__file__).resolve().parents[1]


def _run_snippet(body: str) -> subprocess.CompletedProcess[str]:
    with tempfile.TemporaryDirectory(prefix="phase-space-generalized-metric-test-") as td:
        path = Path(td) / "PhaseSpaceGeneralizedMetricSmoke.lean"
        path.write_text(
            textwrap.dedent(
                f"""\
                import InfoGeometry.Clifford.PhaseSpaceGeneralizedMetric
                import InfoGeometry.Clifford.NeutralPhaseSpaceRankOne

                open scoped InnerProductSpace
                open InfoGeometry.Clifford.NeutralPhaseSpaceCore
                open InfoGeometry.Clifford.NeutralPhaseSpaceDoubledBridge
                open InfoGeometry.Clifford.NeutralPhaseSpaceRankOne
                open InfoGeometry.Clifford.PhaseSpaceGeneralizedMetric
                open InfoGeometry.Clifford.PhaseSpaceGeneralizedMetric.GeneralizedMetricDatum
                open InfoGeometry.Krein

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


class PhaseSpaceGeneralizedMetricTests(unittest.TestCase):
    def test_rank_one_owner_algebra_example_survives(self):
        proc = _run_snippet(
            """
            namespace Scratch.PhaseSpaceGeneralizedMetric

            noncomputable def realMetric : MetricDatum ℝ where
              gFlat := dualRealEquiv.symm
              symmetric := by
                intro x y
                simp [dualRealEquiv, dualRealProjection, dualRealSection, mul_comm]

            example :
                (GeneralizedMetricDatum.ofMetric realMetric).generalizedMetricForm
                    (1, dualRealEquiv.symm 3) (2, dualRealEquiv.symm 5) = 17 := by
              rw [GeneralizedMetricDatum.generalizedMetricForm_ofMetric_apply]
              norm_num [realMetric, dualRealEquiv, dualRealProjection, dualRealSection,
                mul_comm, mul_left_comm, mul_assoc]

            example :
                (GeneralizedMetricDatum.ofMetric realMetric).generalizedMetricForm
                    (1, dualRealEquiv.symm 3) (2, dualRealEquiv.symm 5)
                  =
                (GeneralizedMetricDatum.ofMetric realMetric).generalizedMetricForm
                    (2, dualRealEquiv.symm 5) (1, dualRealEquiv.symm 3) := by
              exact
                GeneralizedMetricDatum.generalizedMetricForm_symm
                  (G := GeneralizedMetricDatum.ofMetric realMetric)
                  (X := (1, dualRealEquiv.symm 3))
                  (Y := (2, dualRealEquiv.symm 5))

            example :
                (GeneralizedMetricDatum.ofMetric realMetric).polarization
                    (1, dualRealEquiv.symm 3)
                  = (3, dualRealEquiv.symm 1) := by
              rw [GeneralizedMetricDatum.ofMetric_polarization]
              change
                (realMetric.gFlat.symm (dualRealEquiv.symm 3), realMetric.gFlat 1)
                  = (3, dualRealEquiv.symm 1)
              refine Prod.ext ?_ ?_
              · simpa [realMetric] using
                  (LinearEquiv.apply_symm_apply dualRealEquiv (3 : ℝ))
              · rfl

            example :
                toDoubledCopyRho realMetric.gFlat
                    ((GeneralizedMetricDatum.ofMetric realMetric).polarization
                      (1, dualRealEquiv.symm 3))
                  =
                modular_j (E := ℝ)
                    (toDoubledCopyRho realMetric.gFlat (1, dualRealEquiv.symm 3)) := by
              have h :=
                congrArg
                  (fun F : PhaseSpaceCarrier ℝ →ₗ[ℝ] DoubledSpace ℝ =>
                    F (1, dualRealEquiv.symm 3))
                  (toDoubledCopyRho_comp_ofMetricPolarization (E := ℝ) realMetric)
              simpa [LinearMap.comp_apply] using h

            end Scratch.PhaseSpaceGeneralizedMetric
            """
        )
        output = _combined_output(proc)
        self.assertEqual(proc.returncode, 0, msg=output)


if __name__ == "__main__":
    unittest.main()
