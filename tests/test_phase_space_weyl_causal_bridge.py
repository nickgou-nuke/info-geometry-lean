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
            variable (Δ : WeylDifferentialOperator ℝ X A)
            variable (γ : WeylTrajectory I X)
            variable (bridge :
              FlatCurvatureChiralScaleBridge
                (CI := CCI.toConformalInference) (Δ := Δ) (γ := γ))
            variable (B : WeylGaugeField X A)
            variable (hFlat : WeylGaugeField.IsFlat (Δ := Δ) B)

            example :
                bridge.lineIntegrator.holonomy bridge.holonomyMap B γ
                  = CCI.toConformalInference.chiralScale :=
              holonomy_eq_chiralScale_of_flat_from_conformal
                (CCI := CCI) (Δ := Δ) (γ := γ) (bridge := bridge) (B := B) hFlat

            example :
                bridge.lineIntegrator.holonomy bridge.holonomyMap B γ
                  =
                    ‖CCI.toConformalInference.spectralChiralProjector
                        * CCI.toConformalInference.metricChiralProjector
                        - CCI.toConformalInference.metricChiralProjector
                            * CCI.toConformalInference.spectralChiralProjector‖₊ :=
              holonomy_eq_projectorObstruction_norm_of_flat_from_leaf
                (CCI := CCI) (R := R) (leaf := leaf) (Δ := Δ) (γ := γ)
                (bridge := bridge) (B := B) hFlat

            example :
                WeylLeafOutputs (CCI := CCI) (Δ := Δ) (γ := γ) :=
              WeylLeafOutputs.ofFlatBridge (CCI := CCI) (Δ := Δ) (γ := γ) (bridge := bridge)

            end WeylLeaf

            end Scratch.PhaseSpaceWeylCausalBridge
            """
        )
        if proc.returncode != 0:
            raise AssertionError(_combined_output(proc))


if __name__ == "__main__":
    unittest.main()
