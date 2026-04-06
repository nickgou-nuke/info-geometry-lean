import subprocess
import tempfile
import textwrap
import unittest
from pathlib import Path


REPO_ROOT = Path(__file__).resolve().parents[1]


def _run_snippet(body: str) -> subprocess.CompletedProcess[str]:
    with tempfile.TemporaryDirectory(prefix="phase-space-conformal-kkt-bridge-test-") as td:
        path = Path(td) / "PhaseSpaceConformalKKTBridgeSmoke.lean"
        path.write_text(
            textwrap.dedent(
                f"""\
                import InfoGeometry.Canonical.PhaseSpaceConformalKKTBridge

                open scoped InnerProductSpace
                open InfoGeometry.Canonical.KKTCore
                open InfoGeometry.Canonical.ConformalUnification
                open InfoGeometry.Canonical.ChiralCartanCore
                open InfoGeometry.Canonical.PhaseSpaceConformalKKTBridge
                open InfoGeometry.Clifford.NeutralPhaseSpaceCore
                open InfoGeometry.Clifford.NeutralPhaseSpaceDoubledBridge
                open InfoGeometry.Quantum
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


class PhaseSpaceConformalKKTBridgeTests(unittest.TestCase):
    def test_owner_kkt_and_conformal_bridge_surfaces_remain_available(self):
        proc = _run_snippet(
            """
            namespace Scratch.PhaseSpaceConformalKKTBridge

            section OwnerToKKT

            variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
            variable (ρ : H ≃ₗ[ℝ] Module.Dual ℝ H)

            example :
                (toDoubledCopyRho (E := H) ρ).comp (phasePlusProjector (E := H))
                  = (plusProjector (doubledSpaceCl11Action (E := H))).toLinearMap.comp
                      (toDoubledCopyRho (E := H) ρ) := by
              simpa using toDoubledCopyRho_comp_phasePlusProjector_eq_KKT_plusProjector (H := H) ρ

            example :
                (toDoubledCopyRho (E := H) ρ).comp (phaseMinusProjector (E := H))
                  = (minusProjector (doubledSpaceCl11Action (E := H))).toLinearMap.comp
                      (toDoubledCopyRho (E := H) ρ) := by
              simpa using toDoubledCopyRho_comp_phaseMinusProjector_eq_KKT_minusProjector (H := H) ρ

            example :
                (toDoubledCopyRho (E := H) ρ).comp (phaseRotation (E := H) ρ)
                  = (dilationOperator (E := H)).toLinearMap.comp (toDoubledCopyRho (E := H) ρ) := by
              simpa using toDoubledCopyRho_comp_phaseRotation_eq_KKT_dilationOperator (H := H) ρ

            end OwnerToKKT

            section KKTToConformal

            variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
            variable [FiniteDimensional ℝ E]
            variable (X : RealSplitCl11Action E)
            variable (CCI : CertifiedConformalInference E)
            variable (hA : IsGOne X CCI.A)
            variable (hAMP : IsGNegOne X CCI.A_MP)
            variable (hAD : IsGNegOne X CCI.A_D)

            example :
                CCI.toConformalInference.D = CCI.toCertifiedInverseKernel.dilationGap := by
              simpa using CertifiedConformalInference.D_eq_dilationGap (CCI := CCI)

            example :
                chiralGrading CCI.toConformalInference
                  = (2 : ℝ) • CCI.toCertifiedInverseKernel.dilationGap := by
              simpa using CertifiedConformalInference.chiralGrading_eq_two_smul_dilationGap (CCI := CCI)

            example :
                IsGZero X CCI.toCertifiedInverseKernel.mpChiralGap := by
              simpa using CertifiedConformalInference.mpChiralGap_isGZero
                (X := X) (CCI := CCI) hA hAMP

            example :
                IsGZero X CCI.toCertifiedInverseKernel.dilationGap := by
              simpa using CertifiedConformalInference.dilationGap_isGZero
                (X := X) (CCI := CCI) hA hAMP

            example :
                IsGZero X CCI.toCertifiedInverseKernel.drazinCoreProj := by
              simpa using CertifiedConformalInference.drazinCoreProj_isGZero
                (X := X) (CCI := CCI) hA hAD

            example :
                IsGZero X CCI.toConformalInference.D := by
              simpa using CertifiedConformalInference.D_isGZero
                (X := X) (CCI := CCI) hA hAMP

            example :
                IsGZero X (chiralGrading CCI.toConformalInference) := by
              simpa using CertifiedConformalInference.chiralGrading_isGZero
                (X := X) (CCI := CCI) hA hAMP

            end KKTToConformal

            section CorrectedOwnerEndpoint

            variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
            variable [FiniteDimensional ℝ H]
            variable (CCI : CertifiedConformalInference (DoubledSpace H))
            variable (hA : IsGOne (doubledSpaceCl11Action (E := H)) CCI.A)
            variable (hAMP : IsGNegOne (doubledSpaceCl11Action (E := H)) CCI.A_MP)

            example :
                IsGZero (doubledSpaceCl11Action (E := H))
                  (chiralGrading CCI.toConformalInference) := by
              simpa using correctedOwner_chiralGrading_isGZero
                (H := H) (CCI := CCI) hA hAMP

            end CorrectedOwnerEndpoint

            end Scratch.PhaseSpaceConformalKKTBridge
            """
        )
        output = _combined_output(proc)
        self.assertEqual(proc.returncode, 0, msg=output)


if __name__ == "__main__":
    unittest.main()
