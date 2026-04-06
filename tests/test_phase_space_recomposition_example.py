import subprocess
import tempfile
import textwrap
import unittest
from pathlib import Path


REPO_ROOT = Path(__file__).resolve().parents[1]


def _run_snippet(body: str) -> subprocess.CompletedProcess[str]:
    with tempfile.TemporaryDirectory(prefix="phase-space-recomposition-example-test-") as td:
        path = Path(td) / "PhaseSpaceRecompositionExampleSmoke.lean"
        path.write_text(
            textwrap.dedent(
                f"""\
                import InfoGeometry.Canonical.PhaseSpaceRecompositionExample

                open scoped InnerProductSpace
                open InfoGeometry.Canonical.GeneralizedMetricRecompositionBridge
                open InfoGeometry.Canonical.PhaseSpaceRecompositionExample
                open InfoGeometry.Clifford.NeutralPhaseSpaceDoubledBridge
                open InfoGeometry.Clifford.NeutralPhaseSpaceRankOne

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


class PhaseSpaceRecompositionExampleTests(unittest.TestCase):
    def test_concrete_recomposition_example_survives(self):
        proc = _run_snippet(
            """
            namespace Scratch.PhaseSpaceRecompositionExample

            example :
                ambientRelativeBridge.projectiveLogDensity 0 = Real.log (2 : ℝ) := by
              exact ambient_projectiveLogDensity_zero

            example :
                ambientRelativeBridge.projectiveLogDensity 1 = -Real.log (2 : ℝ) := by
              exact ambient_projectiveLogDensity_one

            example :
                recompositionData.plusLogDefect = -Real.log (2 : ℝ) := by
              exact plusLogDefect_eq_neg_log_two

            example :
                recompositionData.minusLogDefect = Real.log (2 : ℝ) := by
              exact minusLogDefect_eq_log_two

            example :
                recompositionData.couplingLogDefect = 0 := by
              exact couplingLogDefect_eq_zero

            example :
                recompositionData.exactLogRecomposition := by
              exact exactLogRecomposition

            example :
                recompositionData.exactPotentialRecomposition := by
              exact exactPotentialRecomposition

            example :
                PolarizedRecompositionData.generalizedMetricTwistShadow
                    recompositionData = 0 := by
              exact generalizedMetricTwistShadow_eq_zero

            example :
                toDoubledCopyRho (E := ExampleH) dualRealEquiv.symm
                    (InfoGeometry.Canonical.PhaseSpaceRecompositionBridge.PolarizedRecompositionData.plusPhaseTransportLift
                      recompositionData dualRealEquiv.symm 0)
                  =
                    InfoGeometry.Canonical.GeneralizedMetricRecompositionBridge.PolarizedRecompositionData.plusMetricTransportLift
                      recompositionData 0 := by
              exact plusPhaseTransportLift_realizes_through_doubled_corridor

            example :
                toDoubledCopyRho (E := ExampleH) dualRealEquiv.symm
                    (InfoGeometry.Canonical.PhaseSpaceRecompositionBridge.PolarizedRecompositionData.minusPhaseTransportLift
                      recompositionData dualRealEquiv.symm 0)
                  =
                    InfoGeometry.Canonical.GeneralizedMetricRecompositionBridge.PolarizedRecompositionData.minusMetricTransportLift
                      recompositionData 0 := by
              exact minusPhaseTransportLift_realizes_through_doubled_corridor

            end Scratch.PhaseSpaceRecompositionExample
            """
        )
        output = _combined_output(proc)
        self.assertEqual(proc.returncode, 0, msg=output)


if __name__ == "__main__":
    unittest.main()
