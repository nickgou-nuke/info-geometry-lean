import subprocess
import tempfile
import textwrap
import unittest
from pathlib import Path


REPO_ROOT = Path(__file__).resolve().parents[1]


def _run_snippet(body: str) -> subprocess.CompletedProcess[str]:
    with tempfile.TemporaryDirectory(prefix="clnn-corridor-test-") as td:
        path = Path(td) / "ClNNCorridorSmoke.lean"
        path.write_text(
            textwrap.dedent(
                f"""\
                import InfoGeometry.Canonical.ClNNBottBridge
                import InfoGeometry.KK.ClNNFredholmBridge

                open scoped TensorProduct
                open scoped InnerProductSpace
                open InfoGeometry.Clifford.ClNN
                open InfoGeometry.Canonical.ClNNBottBridge
                open InfoGeometry.KK.ClNNFredholmBridge
                open InfoGeometry.CliffordTower
                open InfoGeometry.Krein
                open InfoGeometry.Quantum
                open InfoGeometry.KK

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


class ClNNCorridorTests(unittest.TestCase):
    def test_clnn_owner_and_bridges_survive(self):
        proc = _run_snippet(
            """
            namespace Scratch.ClNNCorridor

            section

            example (n : ℕ) :
                gammaHeadNullMinus n * gammaHeadNullMinus n = 0 := by
              exact gammaHeadNullMinus_sq n

            example (n : ℕ) :
                gammaHeadNullPlus n * gammaHeadNullPlus n = 0 := by
              exact gammaHeadNullPlus_sq n

            example (n : ℕ) :
                gammaHeadNullMinus n * gammaHeadNullPlus n
                  + gammaHeadNullPlus n * gammaHeadNullMinus n = 1 := by
              exact gammaHeadNullMinus_mul_gammaHeadNullPlus_add_swap n

            example (n : ℕ) (xs : Carrier n) :
                gammaHeadNullMinus n * gammaTail n xs
                  + gammaTail n xs * gammaHeadNullMinus n = 0 := by
              exact gammaHeadNullMinus_mul_gammaTail_add_swap n xs

            example (n : ℕ) :
                InfoGeometry.Canonical.BottPeriodicity.bottStepEquiv n (gammaHeadNullMinus n)
                  = (CliffordAlgebra.ι InfoGeometry.CliffordTower.Q11 ((1 / 2 : ℝ), (1 / 2 : ℝ)))
                      ᵍ⊗ₜ (1 : CliffordAlgebra (Qsplit n)) := by
              exact bottStep_headNullMinus n

            example (n : ℕ) (xs : Carrier n) :
                InfoGeometry.Canonical.BottPeriodicity.bottStepEquiv n
                    (CliffordAlgebra.ι (Quad (n + 1)) (tailLift n xs))
                  = (1 : CliffordAlgebra InfoGeometry.CliffordTower.Q11) ᵍ⊗ₜ
                      (CliffordAlgebra.ι (Qsplit n) xs) := by
              exact bottStep_tailLift n xs

            variable {A B E : Type*}
            variable [NormedRing A] [NormedRing B]
            variable [NormedAlgebra ℝ A] [NormedAlgebra ℝ B]
            variable [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
            variable [KreinSpace (DoubledSpace E)] [KreinGradedModule (DoubledSpace E)]
            variable (X : RealSplitKreinKasparovCycle A B (DoubledSpace E))
            variable (hcl11 : X.cl11 = doubledSpaceCl11Action (E := E))

            example :
                X.K
                  = InfoGeometry.Krein.cl11Rep (E := E)
                      (CliffordAlgebra.ι InfoGeometry.Clifford.splitQ11 (0, 1)) := by
              exact
                RealSplitKreinKasparovCycle.firstStep_rightGenerator_eq_cl11Rep
                  (X := X) hcl11

            end

            end Scratch.ClNNCorridor
            """
        )
        output = _combined_output(proc)
        self.assertEqual(proc.returncode, 0, msg=output)


if __name__ == "__main__":
    unittest.main()
