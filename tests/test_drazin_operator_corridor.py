import subprocess
import tempfile
import textwrap
import unittest
from pathlib import Path


REPO_ROOT = Path(__file__).resolve().parents[1]


def _run_snippet(body: str) -> subprocess.CompletedProcess[str]:
    with tempfile.TemporaryDirectory(prefix="drazin-operator-corridor-test-") as td:
        path = Path(td) / "DrazinOperatorCorridorSmoke.lean"
        path.write_text(
            textwrap.dedent(
                f"""\
                import InfoGeometry.Canonical.DrazinCoreFlow
                import InfoGeometry.Canonical.DrazinDescriptorSystems
                import InfoGeometry.Canonical.EPDefectAlgebra

                open scoped InnerProductSpace
                open InfoGeometry.Canonical

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


class DrazinOperatorCorridorTests(unittest.TestCase):
    def test_drazin_core_descriptor_and_ep_surfaces_remain_available(self):
        proc = _run_snippet(
            """
            namespace Scratch.DrazinOperatorCorridor

            section

            variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
            variable (CIK : CertifiedInverseKernel E) (t : ℝ)
            variable {m : ℕ}

            example :
                CIK.A = CIK.corePart + CIK.nilpotentPart := by
              simpa using CIK.A_eq_corePart_add_nilpotentPart

            example :
                CIK.corePart * CIK.nilpotentPart = 0 := by
              simpa using CIK.corePart_mul_nilpotentPart_eq_zero

            example :
                CIK.nilpotentPart * CIK.corePart = 0 := by
              simpa using CIK.nilpotentPart_mul_corePart_eq_zero

            example :
                CIK.ambientFlow t = CIK.coreFlow t * CIK.nilpotentFlow t := by
              simpa using CIK.ambientFlow_eq_coreFlow_mul_nilpotentFlow t

            example :
                CIK.ambientFlow t = CIK.nilpotentFlow t * CIK.coreFlow t := by
              simpa using CIK.ambientFlow_eq_nilpotentFlow_mul_coreFlow t

            example :
                CIK.mpInverseCommutator = CIK.mpChiralGap := by
              simpa using CIK.mpInverseCommutator_eq_mpChiralGap

            example :
                CIK.mpChiralGap = (2 : ℝ) • CIK.dilationGap := by
              simpa using CIK.mpChiralGap_eq_two_smul_dilationGap

            example :
                CIK.mpInverseCommutator = 0 ↔ CIK.IsEP := by
              simpa using CIK.mpInverseCommutator_eq_zero_iff_isEP

            example
                (hRight : CIK.drazinCoreProj * CIK.mpRightProj = CIK.mpRightProj * CIK.drazinCoreProj) :
                CIK.drazinCoreProj * CIK.dilationGap - CIK.dilationGap * CIK.drazinCoreProj
                  = -((2 : ℝ)⁻¹) • CIK.chiralAnomaly := by
              simpa using
                CIK.spectralProjector_commutator_dilationGap_eq_neg_half_chiralAnomaly_of_mpRightCommute
                  hRight

            end

            end Scratch.DrazinOperatorCorridor
            """
        )
        output = _combined_output(proc)
        self.assertEqual(proc.returncode, 0, msg=output)


if __name__ == "__main__":
    unittest.main()
