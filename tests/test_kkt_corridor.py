import subprocess
import tempfile
import textwrap
import unittest
from pathlib import Path


REPO_ROOT = Path(__file__).resolve().parents[1]


def _run_snippet(body: str) -> subprocess.CompletedProcess[str]:
    with tempfile.TemporaryDirectory(prefix="kkt-corridor-test-") as td:
        path = Path(td) / "KKTCorridorSmoke.lean"
        path.write_text(
            textwrap.dedent(
                f"""\
                import InfoGeometry.Canonical.KKTCore
                import InfoGeometry.Canonical.KKTGeneralizedInverseBridge
                import InfoGeometry.Canonical.KKTGeneralizedMetricBridge
                import InfoGeometry.KK.RealSplitKKTBridge

                open scoped InnerProductSpace
                open InfoGeometry.Canonical
                open InfoGeometry.Canonical.KKTCore
                open InfoGeometry.Canonical.KKTGeneralizedInverseBridge
                open InfoGeometry.Canonical.KKTGeneralizedMetricBridge
                open InfoGeometry.KK.RealSplitKKTBridge

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


class KKTCorridorTests(unittest.TestCase):
    def test_kkt_core_inverse_metric_and_kk_bridges_remain_available(self):
        proc = _run_snippet(
            """
            namespace Scratch.KKTCorridor

            section OperatorBridge

            variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
            variable (X : InfoGeometry.Quantum.RealSplitCl11Action E)
            variable (CIK : CertifiedInverseKernel E)
            variable (hA : IsGOne X CIK.A)
            variable (hAMP : IsGNegOne X CIK.A_MP)
            variable (hAD : IsGNegOne X CIK.A_D)

            example :
                IsGZero X CIK.mpInverseCommutator := by
              simpa using mpInverseCommutator_isGZero (X := X) (CIK := CIK) hA hAMP

            example :
                IsGZero X CIK.mpRightProj := by
              simpa using mpRightProj_isGZero (X := X) (CIK := CIK) hA hAMP

            example :
                IsGZero X CIK.mpLeftProj := by
              simpa using mpLeftProj_isGZero (X := X) (CIK := CIK) hA hAMP

            example :
                IsGZero X CIK.mpChiralGap := by
              simpa using mpChiralGap_isGZero (X := X) (CIK := CIK) hA hAMP

            example :
                IsGZero X CIK.dilationGap := by
              simpa using dilationGap_isGZero (X := X) (CIK := CIK) hA hAMP

            example :
                IsGZero X CIK.drazinCoreProj := by
              simpa using drazinCoreProj_isGZero (X := X) (CIK := CIK) hA hAD

            end OperatorBridge

            section MetricBridge

            variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
            local notation "H2" => InfoGeometry.Krein.DoubledSpace H

            example :
                plusProjector (InfoGeometry.Quantum.doubledSpaceCl11Action (E := H))
                  =
                InfoGeometry.Canonical.GeneralizedMetricCore.GeneralizedMetricSeed.plusProjector
                  (InfoGeometry.Canonical.GeneralizedMetricCore.tomitaGeneralizedMetricSeed :
                    InfoGeometry.Canonical.GeneralizedMetricCore.GeneralizedMetricSeed H) := by
              simpa using canonical_plusProjector_eq_generalizedMetric_plusProjector (H := H)

            example :
                minusProjector (InfoGeometry.Quantum.doubledSpaceCl11Action (E := H))
                  =
                InfoGeometry.Canonical.GeneralizedMetricCore.GeneralizedMetricSeed.minusProjector
                  (InfoGeometry.Canonical.GeneralizedMetricCore.tomitaGeneralizedMetricSeed :
                    InfoGeometry.Canonical.GeneralizedMetricCore.GeneralizedMetricSeed H) := by
              simpa using canonical_minusProjector_eq_generalizedMetric_minusProjector (H := H)

            example :
                InfoGeometry.Krein.dilationOperator (E := H).comp
                    (plusProjector (InfoGeometry.Quantum.doubledSpaceCl11Action (E := H)))
                  =
                (minusProjector (InfoGeometry.Quantum.doubledSpaceCl11Action (E := H))).comp
                  (InfoGeometry.Krein.dilationOperator (E := H)) := by
              simpa using canonical_metric_comp_plusProjector (H := H)

            example :
                InfoGeometry.Krein.dilationOperator (E := H).comp
                    (minusProjector (InfoGeometry.Quantum.doubledSpaceCl11Action (E := H)))
                  =
                (plusProjector (InfoGeometry.Quantum.doubledSpaceCl11Action (E := H))).comp
                  (InfoGeometry.Krein.dilationOperator (E := H)) := by
              simpa using canonical_metric_comp_minusProjector (H := H)

            end MetricBridge

            section KKBridge

            variable {A B H : Type*}
            variable [NormedRing A] [NormedRing B]
            variable [NormedAlgebra ℝ A] [NormedAlgebra ℝ B]
            variable [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
            variable [InfoGeometry.Krein.KreinSpace H] [InfoGeometry.Krein.KreinGradedModule H]
            variable (X : InfoGeometry.KK.RealSplitKreinKasparovCycle A B H)
            variable (hGrade :
              InfoGeometry.Krein.KreinGradedModule.gradeCLM (H := H) = X.cl11.eps)
            variable (a : A) (b : B)

            example :
                IsGZero X.cl11 (X.π a) := by
              simpa using pi_isGZero_of_gradeCLM_eq_eps (X := X) hGrade a

            example :
                IsGZero X.cl11 (X.ρ b) := by
              simpa using rho_isGZero_of_gradeCLM_eq_eps (X := X) hGrade b

            example :
                gZeroPart X.cl11 X.F = 0 := by
              simpa using gZeroPart_F_eq_zero_of_gradeCLM_eq_eps (X := X) hGrade

            example :
                X.F = gOnePart X.cl11 X.F + gNegOnePart X.cl11 X.F := by
              simpa using F_eq_gOnePart_add_gNegOnePart_of_gradeCLM_eq_eps (X := X) hGrade

            end KKBridge

            end Scratch.KKTCorridor
            """
        )
        output = _combined_output(proc)
        self.assertEqual(proc.returncode, 0, msg=output)


if __name__ == "__main__":
    unittest.main()
