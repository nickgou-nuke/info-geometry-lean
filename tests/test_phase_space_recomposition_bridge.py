import subprocess
import tempfile
import textwrap
import unittest
from pathlib import Path


REPO_ROOT = Path(__file__).resolve().parents[1]


def _run_snippet(body: str) -> subprocess.CompletedProcess[str]:
    with tempfile.TemporaryDirectory(prefix="phase-space-recomposition-bridge-test-") as td:
        path = Path(td) / "PhaseSpaceRecompositionBridgeSmoke.lean"
        path.write_text(
            textwrap.dedent(
                f"""\
                import InfoGeometry.Canonical.PhaseSpaceRecompositionBridge

                open scoped InnerProductSpace
                open InfoGeometry.Canonical.RelativeModularRecomposition
                open InfoGeometry.Canonical.GeneralizedMetricRecompositionBridge
                open InfoGeometry.Canonical.PhaseSpaceRecompositionBridge
                open InfoGeometry.Clifford.NeutralPhaseSpaceCore
                open InfoGeometry.Clifford.NeutralPhaseSpaceDoubledBridge
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


class PhaseSpaceRecompositionBridgeTests(unittest.TestCase):
    def test_phase_space_recomposition_bridge_surfaces_remain_available(self):
        proc = _run_snippet(
            """
            namespace Scratch.PhaseSpaceRecompositionBridge

            section

            variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
            variable {α : Type*} [Fintype α] [Nonempty α]
            variable {βplus : Type*} [Fintype βplus] [Nonempty βplus]
            variable {βminus : Type*} [Fintype βminus] [Nonempty βminus]
            variable (G : InfoGeometry.Clifford.PhaseSpaceGeneralizedMetric.GeneralizedMetricDatum H)
            variable (R : PolarizedRecompositionData H α βplus βminus)
            variable (ρ : H ≃ₗ[ℝ] Module.Dual ℝ H)
            variable (bplus : βplus) (bminus : βminus)

            example :
                toDoubledCopyRho (E := H) ρ
                    (InfoGeometry.Canonical.PhaseSpaceRecompositionBridge.PolarizedRecompositionData.plusPhaseTransportLift
                      R ρ bplus)
                  = PolarizedRecompositionData.plusMetricTransportLift R bplus := by
              exact
                InfoGeometry.Canonical.PhaseSpaceRecompositionBridge.PolarizedRecompositionData.plusPhaseTransportLift_realizes_as_plusMetricTransportLift
                  (R := R) (ρ := ρ) (b := bplus)

            example :
                toDoubledCopyRho (E := H) ρ
                    (InfoGeometry.Canonical.PhaseSpaceRecompositionBridge.PolarizedRecompositionData.minusPhaseTransportLift
                      R ρ bminus)
                  = PolarizedRecompositionData.minusMetricTransportLift R bminus := by
              exact
                InfoGeometry.Canonical.PhaseSpaceRecompositionBridge.PolarizedRecompositionData.minusPhaseTransportLift_realizes_as_minusMetricTransportLift
                  (R := R) (ρ := ρ) (b := bminus)

            example :
                phaseMinusProjector (E := H)
                    (InfoGeometry.Canonical.PhaseSpaceRecompositionBridge.PolarizedRecompositionData.plusPhaseTransportLift
                      R ρ bplus)
                  =
                    InfoGeometry.Canonical.PhaseSpaceRecompositionBridge.PolarizedRecompositionData.plusPhaseTransportLift
                      R ρ bplus := by
              exact
                InfoGeometry.Canonical.PhaseSpaceRecompositionBridge.PolarizedRecompositionData.plusPhaseTransportLift_fixed_by_phaseMinusProjector
                  (R := R) (ρ := ρ) (b := bplus)

            example :
                InfoGeometry.Canonical.GeneralizedMetricCore.GeneralizedMetricSeed.minusProjector
                    (InfoGeometry.Canonical.GeneralizedMetricCore.tomitaGeneralizedMetricSeed :
                      InfoGeometry.Canonical.GeneralizedMetricCore.GeneralizedMetricSeed H)
                    (toDoubledCopyRho (E := H) ρ
                      (InfoGeometry.Canonical.PhaseSpaceRecompositionBridge.PolarizedRecompositionData.plusPhaseTransportLift
                        R ρ bplus))
                  =
                    toDoubledCopyRho (E := H) ρ
                      (InfoGeometry.Canonical.PhaseSpaceRecompositionBridge.PolarizedRecompositionData.plusPhaseTransportLift
                        R ρ bplus) := by
              exact
                InfoGeometry.Canonical.PhaseSpaceRecompositionBridge.PolarizedRecompositionData.plusPhaseTransportLift_realize_fixed_by_generalizedMetric_minusProjector
                  (R := R) (ρ := ρ) (b := bplus)

            example
                (hfix :
                  G.minusProjector
                    (InfoGeometry.Canonical.PhaseSpaceRecompositionBridge.PolarizedRecompositionData.plusPhaseTransportLift
                      R ρ bplus)
                  =
                    InfoGeometry.Canonical.PhaseSpaceRecompositionBridge.PolarizedRecompositionData.plusPhaseTransportLift
                      R ρ bplus) :
                (InfoGeometry.Canonical.PhaseSpaceGeneralizedMetricChiralityBridge.realizedMinusProjector
                    (G := G) ρ : Module.End ℝ (InfoGeometry.Krein.DoubledSpace H))
                    (toDoubledCopyRho (E := H) ρ
                      (InfoGeometry.Canonical.PhaseSpaceRecompositionBridge.PolarizedRecompositionData.plusPhaseTransportLift
                        R ρ bplus))
                  =
                    toDoubledCopyRho (E := H) ρ
                      (InfoGeometry.Canonical.PhaseSpaceRecompositionBridge.PolarizedRecompositionData.plusPhaseTransportLift
                        R ρ bplus) := by
              exact
                InfoGeometry.Canonical.PhaseSpaceRecompositionBridge.PolarizedRecompositionData.plusPhaseTransportLift_realize_fixed_by_realizedMinusProjector
                  (G := G) (R := R) (ρ := ρ) (b := bplus) hfix

            example
                (hfix :
                  G.minusProjector
                    (InfoGeometry.Canonical.PhaseSpaceRecompositionBridge.PolarizedRecompositionData.plusPhaseTransportLift
                      R ρ bplus)
                  =
                    InfoGeometry.Canonical.PhaseSpaceRecompositionBridge.PolarizedRecompositionData.plusPhaseTransportLift
                      R ρ bplus) :
                InfoGeometry.Canonical.GeneralizedMetricCore.GeneralizedMetricSeed.minusProjector
                    (InfoGeometry.Canonical.GeneralizedMetricCore.tomitaGeneralizedMetricSeed :
                      InfoGeometry.Canonical.GeneralizedMetricCore.GeneralizedMetricSeed H)
                    (toDoubledCopyRho (E := H) ρ
                      (InfoGeometry.Canonical.PhaseSpaceRecompositionBridge.PolarizedRecompositionData.plusPhaseTransportLift
                        R ρ bplus))
                  =
                    toDoubledCopyRho (E := H) ρ
                      (InfoGeometry.Canonical.PhaseSpaceRecompositionBridge.PolarizedRecompositionData.plusPhaseTransportLift
                        R ρ bplus) := by
            exact
                InfoGeometry.Canonical.PhaseSpaceRecompositionBridge.PolarizedRecompositionData.plusPhaseTransportLift_realize_fixed_by_generalizedMetric_minusProjector
                  (R := R) (ρ := ρ) (b := bplus)

            example :
                phasePlusProjector (E := H)
                    (InfoGeometry.Canonical.PhaseSpaceRecompositionBridge.PolarizedRecompositionData.minusPhaseTransportLift
                      R ρ bminus)
                  =
                    InfoGeometry.Canonical.PhaseSpaceRecompositionBridge.PolarizedRecompositionData.minusPhaseTransportLift
                      R ρ bminus := by
              exact
                InfoGeometry.Canonical.PhaseSpaceRecompositionBridge.PolarizedRecompositionData.minusPhaseTransportLift_fixed_by_phasePlusProjector
                  (R := R) (ρ := ρ) (b := bminus)

            example :
                InfoGeometry.Canonical.GeneralizedMetricCore.GeneralizedMetricSeed.plusProjector
                    (InfoGeometry.Canonical.GeneralizedMetricCore.tomitaGeneralizedMetricSeed :
                      InfoGeometry.Canonical.GeneralizedMetricCore.GeneralizedMetricSeed H)
                    (toDoubledCopyRho (E := H) ρ
                      (InfoGeometry.Canonical.PhaseSpaceRecompositionBridge.PolarizedRecompositionData.minusPhaseTransportLift
                        R ρ bminus))
                  =
                    toDoubledCopyRho (E := H) ρ
                      (InfoGeometry.Canonical.PhaseSpaceRecompositionBridge.PolarizedRecompositionData.minusPhaseTransportLift
                        R ρ bminus) := by
              exact
                InfoGeometry.Canonical.PhaseSpaceRecompositionBridge.PolarizedRecompositionData.minusPhaseTransportLift_realize_fixed_by_generalizedMetric_plusProjector
                  (R := R) (ρ := ρ) (b := bminus)

            example
                (hfix :
                  G.plusProjector
                    (InfoGeometry.Canonical.PhaseSpaceRecompositionBridge.PolarizedRecompositionData.minusPhaseTransportLift
                      R ρ bminus)
                  =
                    InfoGeometry.Canonical.PhaseSpaceRecompositionBridge.PolarizedRecompositionData.minusPhaseTransportLift
                      R ρ bminus) :
                (InfoGeometry.Canonical.PhaseSpaceGeneralizedMetricChiralityBridge.realizedPlusProjector
                    (G := G) ρ : Module.End ℝ (InfoGeometry.Krein.DoubledSpace H))
                    (toDoubledCopyRho (E := H) ρ
                      (InfoGeometry.Canonical.PhaseSpaceRecompositionBridge.PolarizedRecompositionData.minusPhaseTransportLift
                        R ρ bminus))
                  =
                    toDoubledCopyRho (E := H) ρ
                      (InfoGeometry.Canonical.PhaseSpaceRecompositionBridge.PolarizedRecompositionData.minusPhaseTransportLift
                        R ρ bminus) := by
              exact
                InfoGeometry.Canonical.PhaseSpaceRecompositionBridge.PolarizedRecompositionData.minusPhaseTransportLift_realize_fixed_by_realizedPlusProjector
                  (G := G) (R := R) (ρ := ρ) (b := bminus) hfix

            example
                (hfix :
                  G.plusProjector
                    (InfoGeometry.Canonical.PhaseSpaceRecompositionBridge.PolarizedRecompositionData.minusPhaseTransportLift
                      R ρ bminus)
                  =
                    InfoGeometry.Canonical.PhaseSpaceRecompositionBridge.PolarizedRecompositionData.minusPhaseTransportLift
                      R ρ bminus) :
                InfoGeometry.Canonical.GeneralizedMetricCore.GeneralizedMetricSeed.plusProjector
                    (InfoGeometry.Canonical.GeneralizedMetricCore.tomitaGeneralizedMetricSeed :
                      InfoGeometry.Canonical.GeneralizedMetricCore.GeneralizedMetricSeed H)
                    (toDoubledCopyRho (E := H) ρ
                      (InfoGeometry.Canonical.PhaseSpaceRecompositionBridge.PolarizedRecompositionData.minusPhaseTransportLift
                        R ρ bminus))
                  =
                    toDoubledCopyRho (E := H) ρ
                      (InfoGeometry.Canonical.PhaseSpaceRecompositionBridge.PolarizedRecompositionData.minusPhaseTransportLift
                        R ρ bminus) := by
            exact
                InfoGeometry.Canonical.PhaseSpaceRecompositionBridge.PolarizedRecompositionData.minusPhaseTransportLift_realize_fixed_by_generalizedMetric_plusProjector
                  (R := R) (ρ := ρ) (b := bminus)

            example :
                toDoubledCopyRho (E := H) ρ
                    (InfoGeometry.Canonical.PhaseSpaceRecompositionBridge.PolarizedRecompositionData.plusPhaseTransportLift
                      R ρ bplus)
                  ∈ minusSheet (E := H) := by
              exact
                InfoGeometry.Canonical.PhaseSpaceRecompositionBridge.PolarizedRecompositionData.plusPhaseTransportLift_realizes_to_minusSheet
                  (R := R) (ρ := ρ) (b := bplus)

            example :
                toDoubledCopyRho (E := H) ρ
                    (InfoGeometry.Canonical.PhaseSpaceRecompositionBridge.PolarizedRecompositionData.minusPhaseTransportLift
                      R ρ bminus)
                  ∈ plusSheet (E := H) := by
              exact
                InfoGeometry.Canonical.PhaseSpaceRecompositionBridge.PolarizedRecompositionData.minusPhaseTransportLift_realizes_to_plusSheet
                  (R := R) (ρ := ρ) (b := bminus)

            example :
                R.couplingLogDefect
                  = PolarizedRecompositionData.generalizedMetricTwistShadow R := by
              exact
                InfoGeometry.Canonical.PhaseSpaceRecompositionBridge.PolarizedRecompositionData.phaseTransport_descends_to_generalizedMetricTwistShadow
                  (R := R)

            end

            section CountJunction

            variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
            variable {α : Type*} [Fintype α] [Nonempty α]
            variable {nPlus : Nat} [Nonempty (Fin nPlus)]
            variable {nMinus : Nat} [Nonempty (Fin nMinus)]
            variable [MeasurableSpace (Fin nPlus)] [MeasurableSingletonClass (Fin nPlus)]
            variable [Countable (Fin nPlus)]
            variable [MeasurableSpace (Fin nMinus)] [MeasurableSingletonClass (Fin nMinus)]
            variable [Countable (Fin nMinus)]
            variable (R : PolarizedRecompositionData H α (Fin nPlus) (Fin nMinus))
            variable (ρ : H ≃ₗ[ℝ] Module.Dual ℝ H)
            variable (countsPlus refPlus :
              InfoGeometry.Canonical.RelativePotentialCountBridge.RelativeCounts nPlus)
            variable (hcountsPlus : ∀ i : Fin nPlus, 0 < countsPlus i)
            variable (hrefPlus : ∀ i : Fin nPlus, 0 < refPlus i)
            variable (countsMinus refMinus :
              InfoGeometry.Canonical.RelativePotentialCountBridge.RelativeCounts nMinus)
            variable (hcountsMinus : ∀ i : Fin nMinus, 0 < countsMinus i)
            variable (hrefMinus : ∀ i : Fin nMinus, 0 < refMinus i)
            variable (iPlus : Fin nPlus) (iMinus : Fin nMinus)

            example
                (hplusSource : R.polarized.plus.data.localSource =
                  InfoGeometry.Canonical.RelativePotentialCountBridge.countRay countsPlus hcountsPlus)
                (hplusTarget : R.polarized.plus.data.localTarget =
                  InfoGeometry.Canonical.RelativePotentialCountBridge.countRay refPlus hrefPlus) :
                True := by
              have _ :=
                InfoGeometry.Canonical.PhaseSpaceRecompositionBridge.PolarizedRecompositionData.plus_phaseSpace_projectiveCount_junction_of_countRays
                  (R := R) (ρ := ρ) (counts := countsPlus) (ref := refPlus)
                  (hcounts := hcountsPlus) (href := hrefPlus)
                  (hsource := hplusSource) (htarget := hplusTarget) (i := iPlus)
              trivial

            example
                (hplusSource : R.polarized.plus.data.localSource =
                  InfoGeometry.Canonical.RelativePotentialCountBridge.countRay countsPlus hcountsPlus)
                (hplusTarget : R.polarized.plus.data.localTarget =
                  InfoGeometry.Canonical.RelativePotentialCountBridge.countRay refPlus hrefPlus)
                (hminusSource : R.polarized.minus.data.localSource =
                  InfoGeometry.Canonical.RelativePotentialCountBridge.countRay countsMinus hcountsMinus)
                (hminusTarget : R.polarized.minus.data.localTarget =
                  InfoGeometry.Canonical.RelativePotentialCountBridge.countRay refMinus hrefMinus) :
                True := by
              have _ :=
                InfoGeometry.Canonical.PhaseSpaceRecompositionBridge.PolarizedRecompositionData.phaseSpace_projectiveCount_weld_of_countRays
                  (R := R) (ρ := ρ)
                  (countsPlus := countsPlus) (refPlus := refPlus)
                  (hcountsPlus := hcountsPlus) (hrefPlus := hrefPlus)
                  (hplusSource := hplusSource) (hplusTarget := hplusTarget)
                  (countsMinus := countsMinus) (refMinus := refMinus)
                  (hcountsMinus := hcountsMinus) (hrefMinus := hrefMinus)
                  (hminusSource := hminusSource) (hminusTarget := hminusTarget)
                  (iPlus := iPlus) (iMinus := iMinus)
              trivial

            example
                (hplusSource : R.polarized.plus.data.localSource =
                  InfoGeometry.Canonical.RelativePotentialCountBridge.countRay countsPlus hcountsPlus)
                (hplusTarget : R.polarized.plus.data.localTarget =
                  InfoGeometry.Canonical.RelativePotentialCountBridge.countRay refPlus hrefPlus)
                (hminusSource : R.polarized.minus.data.localSource =
                  InfoGeometry.Canonical.RelativePotentialCountBridge.countRay countsMinus hcountsMinus)
                (hminusTarget : R.polarized.minus.data.localTarget =
                  InfoGeometry.Canonical.RelativePotentialCountBridge.countRay refMinus hrefMinus) :
                True := by
              have _ :=
                InfoGeometry.Canonical.PhaseSpaceRecompositionBridge.PolarizedRecompositionData.phaseSpace_projectiveCount_weld_identifies_twistShadow_of_countRays
                  (R := R) (ρ := ρ)
                  (countsPlus := countsPlus) (refPlus := refPlus)
                  (hcountsPlus := hcountsPlus) (hrefPlus := hrefPlus)
                  (hplusSource := hplusSource) (hplusTarget := hplusTarget)
                  (countsMinus := countsMinus) (refMinus := refMinus)
                  (hcountsMinus := hcountsMinus) (hrefMinus := hrefMinus)
                  (hminusSource := hminusSource) (hminusTarget := hminusTarget)
                  (iPlus := iPlus) (iMinus := iMinus)
              trivial

            end CountJunction

            end Scratch.PhaseSpaceRecompositionBridge
            """
        )
        output = _combined_output(proc)
        self.assertEqual(proc.returncode, 0, msg=output)


if __name__ == "__main__":
    unittest.main()
