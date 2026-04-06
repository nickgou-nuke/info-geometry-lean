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
                InfoGeometry.Canonical.PhaseSpaceRecompositionBridge.PolarizedRecompositionData.plusPhaseTransportLift_realize_fixed_by_generalizedMetric_minusProjector_of_realizedIdentification
                  (G := G) (R := R) (ρ := ρ) (b := bplus) hfix

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
                InfoGeometry.Canonical.PhaseSpaceRecompositionBridge.PolarizedRecompositionData.minusPhaseTransportLift_realize_fixed_by_generalizedMetric_plusProjector_of_realizedIdentification
                  (G := G) (R := R) (ρ := ρ) (b := bminus) hfix

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

            end Scratch.PhaseSpaceRecompositionBridge
            """
        )
        output = _combined_output(proc)
        self.assertEqual(proc.returncode, 0, msg=output)


if __name__ == "__main__":
    unittest.main()
