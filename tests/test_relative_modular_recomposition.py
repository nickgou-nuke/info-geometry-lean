import subprocess
import tempfile
import textwrap
import unittest
from pathlib import Path


REPO_ROOT = Path(__file__).resolve().parents[1]


def _run_snippet(body: str) -> subprocess.CompletedProcess[str]:
    with tempfile.TemporaryDirectory(prefix="relative-modular-recomposition-test-") as td:
        path = Path(td) / "RelativeModularRecompositionSmoke.lean"
        path.write_text(
            textwrap.dedent(
                f"""\
                import InfoGeometry.Canonical.RelativeModularRecomposition

                open scoped InnerProductSpace
                open InfoGeometry.Canonical.RelativeModularRecomposition

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


class RelativeModularRecompositionTests(unittest.TestCase):
    def test_recomposition_surface_theorems_remain_available(self):
        proc = _run_snippet(
            """
            namespace Scratch.RelativeModularRecomposition

            section

            variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
            variable {α : Type*} [Fintype α] [Nonempty α]
            variable {βplus : Type*} [Fintype βplus] [Nonempty βplus]
            variable {βminus : Type*} [Fintype βminus] [Nonempty βminus]
            variable (R : PolarizedRecompositionData H α βplus βminus)
            variable (bplus : βplus) (bminus : βminus)

            example :
                R.recomposedModularPotential bplus bminus = -R.recomposedLogDensity bplus bminus := by
              simpa using
                PolarizedRecompositionData.recomposedModularPotential_eq_neg_recomposedLogDensity
                  (R := R) (bplus := bplus) (bminus := bminus)

            example (hcoupling : R.couplingLogDefect = 0) :
                R.recomposedLogDensity bplus bminus = R.recomposedCommonCarrierLogDensity bplus bminus := by
              simpa using
                PolarizedRecompositionData.recomposedLogDensity_eq_commonCarrier_of_vanishingCoupling
                  (R := R) (hcoupling := hcoupling) (bplus := bplus) (bminus := bminus)

            example
                (hplus : R.polarized.plus.data.sourceLogShift = R.polarized.plus.data.targetLogShift)
                (hminus : R.polarized.minus.data.sourceLogShift = R.polarized.minus.data.targetLogShift) :
                R.couplingLogDefect = 0 := by
              simpa using
                PolarizedRecompositionData.couplingLogDefect_eq_zero_of_sectorwiseExact
                  (R := R) (hplus := hplus) (hminus := hminus)

            example
                (hplus : R.polarized.plus.data.sourceLogShift = R.polarized.plus.data.targetLogShift)
                (hminus : R.polarized.minus.data.sourceLogShift = R.polarized.minus.data.targetLogShift) :
                R.recomposedModularPotential bplus bminus
                  = R.recomposedCommonCarrierModularPotential bplus bminus := by
              simpa using
                PolarizedRecompositionData.recomposedModularPotential_eq_commonCarrier_of_sectorwiseExact
                  (R := R) (hplus := hplus) (hminus := hminus) (bplus := bplus) (bminus := bminus)

            example :
                R.vanishingCoupling ↔ R.exactLogRecomposition := by
              simpa using
                PolarizedRecompositionData.vanishingCoupling_iff_exactLogRecomposition (R := R)

            example :
                R.vanishingCoupling ↔ R.exactPotentialRecomposition := by
              simpa using
                PolarizedRecompositionData.vanishingCoupling_iff_exactPotentialRecomposition
                  (R := R)

            example :
                R.exactLogRecomposition ↔ R.exactPotentialRecomposition := by
              simpa using
                PolarizedRecompositionData.exactLogRecomposition_iff_exactPotentialRecomposition
                  (R := R)

            example
                (hexact : R.sectorwiseExact) :
                R.vanishingCoupling := by
              simpa using
                PolarizedRecompositionData.vanishingCoupling_of_sectorwiseExact
                  (R := R) (hexact := hexact)

            example
                (hexact : R.sectorwiseExact) :
                R.exactLogRecomposition := by
              simpa using
                PolarizedRecompositionData.exactLogRecomposition_of_sectorwiseExact
                  (R := R) (hexact := hexact)

            example
                (hexact : R.sectorwiseExact) :
                R.exactPotentialRecomposition := by
              simpa using
                PolarizedRecompositionData.exactPotentialRecomposition_of_sectorwiseExact
                  (R := R) (hexact := hexact)

            end

            end Scratch.RelativeModularRecomposition
            """
        )
        output = _combined_output(proc)
        self.assertEqual(proc.returncode, 0, msg=output)


if __name__ == "__main__":
    unittest.main()
