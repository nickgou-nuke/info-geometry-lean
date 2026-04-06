import subprocess
import tempfile
import textwrap
import unittest
from pathlib import Path


REPO_ROOT = Path(__file__).resolve().parents[1]


def _run_snippet(body: str) -> subprocess.CompletedProcess[str]:
    with tempfile.TemporaryDirectory(prefix="phase-space-weyl-causal-bridge-test-") as td:
        path = Path(td) / "PhaseSpaceWeylCausalBridgeSmoke.lean"
        path.write_text(
            textwrap.dedent(
                f"""\
                import InfoGeometry.Canonical.PhaseSpaceWeylCausalBridge

                open scoped InnerProductSpace
                open InfoGeometry.Canonical.PhaseSpaceWeylCausalBridge
                open InfoGeometry.Canonical.WeylTransportBridge
                open InfoGeometry.Canonical.ConformalUnification
                open InfoGeometry.Canonical
                open InfoGeometry.Canonical.RelativeModularRecomposition
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


def _ensure_built() -> subprocess.CompletedProcess[str]:
    return subprocess.run(
        ["lake", "build", "InfoGeometry.Canonical.PhaseSpaceWeylCausalBridge"],
        cwd=REPO_ROOT,
        text=True,
        capture_output=True,
    )


def _combined_output(proc: subprocess.CompletedProcess[str]) -> str:
    return f"{proc.stdout}\n{proc.stderr}"


class PhaseSpaceWeylCausalBridgeTests(unittest.TestCase):
    def test_weyl_causal_bridge_surface(self) -> None:
        build = _ensure_built()
        if build.returncode != 0:
            raise AssertionError(_combined_output(build))
        proc = _run_snippet(
            """
            namespace Scratch.PhaseSpaceWeylCausalBridge

            section WeylLeaf

            variable {I X A E : Type*} [Fintype I]
            variable [AddCommGroup A] [Module ℝ A]
            variable [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
            variable [FiniteDimensional ℝ E]
            variable [Nontrivial E]
            variable {α βplus βminus : Type*}
            variable [Fintype α] [Nonempty α]
            variable [Fintype βplus] [Nonempty βplus]
            variable [Fintype βminus] [Nonempty βminus]

            variable (CCI : CertifiedConformalInference (DoubledSpace E))
            variable (R : PolarizedRecompositionData E α βplus βminus)
            variable (leaf : InfoGeometry.Canonical.PhaseSpaceCausalFlowBridge.LeafOutputs
              E α βplus βminus CCI R)
            variable (CIK : InfoGeometry.Canonical.CertifiedInverseKernel (DoubledSpace E))
            variable (trunk :
              InfoGeometry.Canonical.PhaseSpaceCausalFlowBridge.TrunkOutputs
                E α βplus βminus CIK CCI R)
            variable (Δ : WeylDifferentialOperator ℝ X A)
            variable (γ : WeylTrajectory I X)
            variable (bridge :
              FlatCurvatureProjectorObstructionBridge
                (CI := CCI.toConformalInference) (Δ := Δ) (γ := γ))
            variable (B : WeylGaugeField X A)
            variable (hFlat : WeylGaugeField.IsFlat (Δ := Δ) B)
            variable (hA :
              InfoGeometry.Canonical.KKTCore.IsGOne
                (InfoGeometry.Quantum.doubledSpaceCl11Action (E := E)) CCI.A)
            variable (hAMP :
              InfoGeometry.Canonical.KKTCore.IsGNegOne
                (InfoGeometry.Quantum.doubledSpaceCl11Action (E := E)) CCI.A_MP)
            variable (hAD :
              InfoGeometry.Canonical.KKTCore.IsGNegOne
                (InfoGeometry.Quantum.doubledSpaceCl11Action (E := E)) CCI.A_D)
            variable (hNonComm :
              CCI.toConformalInference.P_D.comp CCI.toConformalInference.P_MP
                ≠ CCI.toConformalInference.P_MP.comp CCI.toConformalInference.P_D)

            example :
                WeylLeafOutputs (CCI := CCI) (Δ := Δ) (γ := γ) :=
              WeylLeafOutputs.ofFlatBridge
                (CCI := CCI) (Δ := Δ) (γ := γ) (bridge := bridge)

            example :
                CCI.toConformalInference.projectorObstruction
                  =
                    CCI.toConformalInference.spectralChiralProjector
                      * CCI.toConformalInference.metricChiralProjector
                      - CCI.toConformalInference.metricChiralProjector
                          * CCI.toConformalInference.spectralChiralProjector := by
              exact
                ConformalInference.projectorObstruction_eq_commutator
                  (CI := CCI.toConformalInference)

            example :
                InfoGeometry.Canonical.KKTCore.IsGZero
                  (InfoGeometry.Quantum.doubledSpaceCl11Action (E := E))
                  CCI.toConformalInference.projectorObstruction := by
              exact
                ConformalInference.projectorObstruction_isGZero_of_kkt_wings
                  (CI := CCI.toConformalInference)
                  (X := InfoGeometry.Quantum.doubledSpaceCl11Action (E := E))
                  hA hAMP hAD

            example
                (hObsG0 :
                  InfoGeometry.Canonical.KKTCore.IsGZero
                    (InfoGeometry.Quantum.doubledSpaceCl11Action (E := E))
                    CCI.toConformalInference.projectorObstruction) :
                let X0 : InfoGeometry.Quantum.RealSplitCl11Action (DoubledSpace E) :=
                  InfoGeometry.Quantum.doubledSpaceCl11Action (E := E)
                bridge.lineIntegrator.holonomy bridge.holonomyMap B γ
                  = ‖InfoGeometry.Canonical.KKTCore.gZeroPart X0
                      CCI.toConformalInference.projectorObstruction‖₊ := by
              simpa using
                holonomy_eq_gZeroPart_projectorObstruction_nnnorm_of_flat_of_projectorObstruction_isGZero
                  (CCI := CCI) (Δ := Δ) (γ := γ) (bridge := bridge) (B := B) hFlat hObsG0

            example :
                InfoGeometry.Canonical.KKTCore.gOnePart
                    (InfoGeometry.Quantum.doubledSpaceCl11Action (E := E))
                    CCI.toConformalInference.projectorObstruction = 0 := by
              exact
                ConformalInference.projectorObstruction_gOnePart_eq_zero_of_kkt_wings
                  (CI := CCI.toConformalInference)
                  (X := InfoGeometry.Quantum.doubledSpaceCl11Action (E := E))
                  hA hAMP hAD

            example :
                InfoGeometry.Canonical.KKTCore.gNegOnePart
                    (InfoGeometry.Quantum.doubledSpaceCl11Action (E := E))
                    CCI.toConformalInference.projectorObstruction = 0 := by
              exact
                ConformalInference.projectorObstruction_gNegOnePart_eq_zero_of_kkt_wings
                  (CI := CCI.toConformalInference)
                  (X := InfoGeometry.Quantum.doubledSpaceCl11Action (E := E))
                  hA hAMP hAD

            example :
                CCI.toConformalInference.projectorObstruction
                  =
                    InfoGeometry.Canonical.KKTCore.plusProjector
                        (InfoGeometry.Quantum.doubledSpaceCl11Action (E := E))
                      * CCI.toConformalInference.projectorObstruction
                      * InfoGeometry.Canonical.KKTCore.plusProjector
                          (InfoGeometry.Quantum.doubledSpaceCl11Action (E := E))
                    + InfoGeometry.Canonical.KKTCore.minusProjector
                        (InfoGeometry.Quantum.doubledSpaceCl11Action (E := E))
                      * CCI.toConformalInference.projectorObstruction
                      * InfoGeometry.Canonical.KKTCore.minusProjector
                          (InfoGeometry.Quantum.doubledSpaceCl11Action (E := E)) := by
              exact
                ConformalInference.projectorObstruction_eq_diagonal_blocks_of_kkt_wings
                  (CI := CCI.toConformalInference)
                  (X := InfoGeometry.Quantum.doubledSpaceCl11Action (E := E))
                  hA hAMP hAD

            example :
                CCI.toConformalInference.projectorObstruction
                  =
                    InfoGeometry.Canonical.KKTCore.plusProjector
                        (InfoGeometry.Quantum.doubledSpaceCl11Action (E := E))
                      * CCI.toConformalInference.projectorObstruction
                      * InfoGeometry.Canonical.KKTCore.plusProjector
                          (InfoGeometry.Quantum.doubledSpaceCl11Action (E := E))
                    + InfoGeometry.Canonical.KKTCore.minusProjector
                        (InfoGeometry.Quantum.doubledSpaceCl11Action (E := E))
                      * CCI.toConformalInference.projectorObstruction
                      * InfoGeometry.Canonical.KKTCore.minusProjector
                          (InfoGeometry.Quantum.doubledSpaceCl11Action (E := E))
                  ∧
                  InfoGeometry.Canonical.KKTCore.plusProjector
                    (InfoGeometry.Quantum.doubledSpaceCl11Action (E := E))
                      * CCI.toConformalInference.projectorObstruction *
                    InfoGeometry.Canonical.KKTCore.minusProjector
                      (InfoGeometry.Quantum.doubledSpaceCl11Action (E := E)) = 0
                  ∧
                  InfoGeometry.Canonical.KKTCore.minusProjector
                    (InfoGeometry.Quantum.doubledSpaceCl11Action (E := E))
                      * CCI.toConformalInference.projectorObstruction *
                    InfoGeometry.Canonical.KKTCore.plusProjector
                      (InfoGeometry.Quantum.doubledSpaceCl11Action (E := E)) = 0
                  ∧
                  bridge.lineIntegrator.holonomy bridge.holonomyMap B γ
                    = ‖CCI.toConformalInference.projectorObstruction‖₊ := by
              exact
                leaf_projectorObstruction_diagonal_blocks_and_holonomy_eq_projectorObstruction_nnnorm_of_flat
                  (CCI := CCI) (R := R) (leaf := leaf)
                  (Δ := Δ) (γ := γ) (bridge := bridge) (B := B) hFlat

            example :
                CCI.toConformalInference.projectorObstruction
                  =
                    InfoGeometry.Canonical.KKTCore.plusProjector
                        (InfoGeometry.Quantum.doubledSpaceCl11Action (E := E))
                      * CCI.toConformalInference.projectorObstruction
                      * InfoGeometry.Canonical.KKTCore.plusProjector
                          (InfoGeometry.Quantum.doubledSpaceCl11Action (E := E))
                    + InfoGeometry.Canonical.KKTCore.minusProjector
                        (InfoGeometry.Quantum.doubledSpaceCl11Action (E := E))
                      * CCI.toConformalInference.projectorObstruction
                      * InfoGeometry.Canonical.KKTCore.minusProjector
                          (InfoGeometry.Quantum.doubledSpaceCl11Action (E := E))
                  ∧
                  InfoGeometry.Canonical.KKTCore.plusProjector
                    (InfoGeometry.Quantum.doubledSpaceCl11Action (E := E))
                      * CCI.toConformalInference.projectorObstruction *
                    InfoGeometry.Canonical.KKTCore.minusProjector
                      (InfoGeometry.Quantum.doubledSpaceCl11Action (E := E)) = 0
                  ∧
                  InfoGeometry.Canonical.KKTCore.minusProjector
                    (InfoGeometry.Quantum.doubledSpaceCl11Action (E := E))
                      * CCI.toConformalInference.projectorObstruction *
                    InfoGeometry.Canonical.KKTCore.plusProjector
                      (InfoGeometry.Quantum.doubledSpaceCl11Action (E := E)) = 0
                  ∧
                  bridge.lineIntegrator.holonomy bridge.holonomyMap B γ
                    = ‖CCI.toConformalInference.projectorObstruction‖₊ := by
              exact
                trunk_projectorObstruction_diagonal_blocks_and_holonomy_eq_projectorObstruction_nnnorm_of_flat
                  (CIK := CIK) (CCI := CCI) (R := R) (trunk := trunk)
                  (Δ := Δ) (γ := γ) (bridge := bridge) (B := B) hFlat

            example :
                CCI.toConformalInference.projectorObstruction
                  =
                    InfoGeometry.Canonical.KKTCore.plusProjector
                        (InfoGeometry.Quantum.doubledSpaceCl11Action (E := E))
                      * CCI.toConformalInference.projectorObstruction
                      * InfoGeometry.Canonical.KKTCore.plusProjector
                          (InfoGeometry.Quantum.doubledSpaceCl11Action (E := E))
                    + InfoGeometry.Canonical.KKTCore.minusProjector
                        (InfoGeometry.Quantum.doubledSpaceCl11Action (E := E))
                      * CCI.toConformalInference.projectorObstruction
                      * InfoGeometry.Canonical.KKTCore.minusProjector
                          (InfoGeometry.Quantum.doubledSpaceCl11Action (E := E))
                  ∧
                  InfoGeometry.Canonical.KKTCore.plusProjector
                    (InfoGeometry.Quantum.doubledSpaceCl11Action (E := E))
                      * CCI.toConformalInference.projectorObstruction *
                    InfoGeometry.Canonical.KKTCore.minusProjector
                      (InfoGeometry.Quantum.doubledSpaceCl11Action (E := E)) = 0
                  ∧
                  InfoGeometry.Canonical.KKTCore.minusProjector
                    (InfoGeometry.Quantum.doubledSpaceCl11Action (E := E))
                      * CCI.toConformalInference.projectorObstruction *
                    InfoGeometry.Canonical.KKTCore.plusProjector
                      (InfoGeometry.Quantum.doubledSpaceCl11Action (E := E)) = 0
                  ∧
                  bridge.lineIntegrator.holonomy bridge.holonomyMap B γ
                    = ‖CCI.toConformalInference.projectorObstruction‖₊ := by
              exact
                kkt_wings_projectorObstruction_diagonal_blocks_and_holonomy_eq_projectorObstruction_nnnorm_of_flat
                  (CCI := CCI) hA hAMP hAD
                  (Δ := Δ) (γ := γ) (bridge := bridge) (B := B) hFlat

            example :
                bridge.lineIntegrator.holonomy bridge.holonomyMap B γ ≠ 0 := by
              exact
                holonomy_ne_zero_of_flat_from_conformal_of_noncommute
                  (CCI := CCI)
                  (Δ := Δ)
                  (γ := γ)
                  (bridge := bridge)
                  (B := B)
                  hFlat
                  hNonComm

            end WeylLeaf

            end Scratch.PhaseSpaceWeylCausalBridge
            """
        )
        if proc.returncode != 0:
            raise AssertionError(_combined_output(proc))


if __name__ == "__main__":
    unittest.main()
