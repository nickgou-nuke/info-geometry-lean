import subprocess
import tempfile
import textwrap
import unittest
from pathlib import Path

"""
Smoke regression for the lowest neutral phase-space lane.

This test is intentionally narrow. It checks only that the corrected owner
surface and the rank-one anchor remain available from Lean:

- the neutral owner on `E × E*`,
- the zero-leg owner lemmas,
- the explicit `ℝ* ≃ ℝ` rank-one duality,
- the exact rank-one identification with `splitQ11`,
- and the induced Clifford equivalence.

It does not try to cover the later doubled/KKT/generalized-metric/recomposition
bridges. Those belong to their own corridor tests.
"""


REPO_ROOT = Path(__file__).resolve().parents[1]


def _run_snippet(body: str) -> subprocess.CompletedProcess[str]:
    with tempfile.TemporaryDirectory(prefix="neutral-phase-space-test-") as td:
        path = Path(td) / "NeutralPhaseSpaceCorridorSmoke.lean"
        path.write_text(
            textwrap.dedent(
                f"""\
                import InfoGeometry.Clifford.NeutralPhaseSpaceRankOne

                open InfoGeometry.Clifford.NeutralPhaseSpaceCore
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


class NeutralPhaseSpaceCorridorSmokeTests(unittest.TestCase):
    def test_owner_and_rank_one_anchor_survive(self):
        proc = _run_snippet(
            """
            namespace Scratch.NeutralPhaseSpaceCorridor

            section

            variable {E : Type*} [AddCommGroup E] [Module ℝ E]

            example (x : E) :
                canonicalNeutralForm (E := E) (x, (0 : Module.Dual ℝ E)) = 0 := by
              exact canonicalNeutralForm_snd_zero (E := E) x

            example (ξ : Module.Dual ℝ E) :
                canonicalNeutralForm (E := E) (0, ξ) = 0 := by
              exact canonicalNeutralForm_fst_zero (E := E) ξ

            example (ξ : Module.Dual ℝ ℝ) :
                dualRealSection (dualRealProjection ξ) = ξ := by
              exact dualRealSection_projection ξ

            example (r : ℝ) :
                dualRealProjection (dualRealSection r) = r := by
              exact dualRealProjection_section r

            example (X : PhaseSpaceCarrier ℝ) :
                InfoGeometry.Clifford.splitQ11 (rankOneIsometry X)
                  = canonicalNeutralForm (E := ℝ) X := by
              exact rankOneIsometry_apply X

            noncomputable example :
                NeutralPhaseClifford ℝ ≃ₐ[ℝ] CliffordAlgebra InfoGeometry.Clifford.splitQ11 :=
              rankOneCliffordEquiv

            end

            end Scratch.NeutralPhaseSpaceCorridor
            """
        )
        output = _combined_output(proc)
        self.assertEqual(proc.returncode, 0, msg=output)


if __name__ == "__main__":
    unittest.main()
