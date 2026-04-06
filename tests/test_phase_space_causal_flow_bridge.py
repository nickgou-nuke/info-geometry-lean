import subprocess
import tempfile
import textwrap
import unittest
from pathlib import Path


REPO_ROOT = Path(__file__).resolve().parents[1]


def _run_snippet(body: str) -> subprocess.CompletedProcess[str]:
    with tempfile.TemporaryDirectory(prefix="phase-space-causal-flow-bridge-test-") as td:
        path = Path(td) / "PhaseSpaceCausalFlowBridgeSmoke.lean"
        path.write_text(
            textwrap.dedent(
                f"""\
                import InfoGeometry.Canonical.PhaseSpaceCausalFlowBridge

                open scoped InnerProductSpace
                open InfoGeometry.Canonical.KKTCore
                open InfoGeometry.Canonical.PhaseSpaceCausalFlowBridge
                open InfoGeometry.Canonical.RelativeModularRecomposition
                open InfoGeometry.Canonical.GeneralizedMetricRecompositionBridge
                open InfoGeometry.Canonical
                open InfoGeometry.Canonical.ConformalUnification
                open InfoGeometry.Canonical.ChiralCartanCore
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


def _ensure_built() -> subprocess.CompletedProcess[str]:
    return subprocess.run(
        ["lake", "build", "InfoGeometry.Canonical.PhaseSpaceCausalFlowBridge"],
        cwd=REPO_ROOT,
        text=True,
        capture_output=True,
    )


def _combined_output(proc: subprocess.CompletedProcess[str]) -> str:
    return f"{proc.stdout}\n{proc.stderr}"


class PhaseSpaceCausalFlowBridgeTests(unittest.TestCase):
    def test_causal_flow_bridge_exposes_trunk_and_leaves(self) -> None:
        build = _ensure_built()
        if build.returncode != 0:
            raise AssertionError(_combined_output(build))
        proc = _run_snippet(
            """
            namespace Scratch.PhaseSpaceCausalFlowBridge

            section OwnerToKKT

            variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
            variable (ρ : H ≃ₗ[ℝ] Module.Dual ℝ H)

            example :
                (toDoubledCopyRho (E := H) ρ).comp (phaseRotation (E := H) ρ)
                  = (dilationOperator (E := H)).toLinearMap.comp
                      (toDoubledCopyRho (E := H) ρ) := by
              simpa using
                (toDoubledCopyRho_comp_phaseRotation_eq_KKT_dilationOperator (H := H) ρ)

            end OwnerToKKT

            section Leaves

            variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
            variable [FiniteDimensional ℝ H]
            variable {α βplus βminus : Type*}
            variable [Fintype α] [Nonempty α]
            variable [Fintype βplus] [Nonempty βplus]
            variable [Fintype βminus] [Nonempty βminus]

            example (R : PolarizedRecompositionData H α βplus βminus) :
                R.couplingLogDefect = PolarizedRecompositionData.generalizedMetricTwistShadow R := by
              exact
                (phaseTransport_descends_to_generalizedMetricTwistShadow (H := H) (R := R))

            end Leaves

            section KKTDefects

            variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
            variable (CIK : InfoGeometry.Canonical.CertifiedInverseKernel (DoubledSpace H))
            variable (hA : IsGOne (doubledSpaceCl11Action (E := H)) CIK.A)
            variable (hAMP : IsGNegOne (doubledSpaceCl11Action (E := H)) CIK.A_MP)

            example :
                IsGZero (doubledSpaceCl11Action (E := H)) CIK.mpChiralGap :=
              correctedOwner_mpChiralGap_isGZero (H := H) (CIK := CIK) hA hAMP

            end KKTDefects

            section TrunkOutputs

            variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
            variable [FiniteDimensional ℝ H]
            variable {α βplus βminus : Type*}
            variable [Fintype α] [Nonempty α]
            variable [Fintype βplus] [Nonempty βplus]
            variable [Fintype βminus] [Nonempty βminus]
            variable (CIK : InfoGeometry.Canonical.CertifiedInverseKernel (DoubledSpace H))
            variable (CCI : CertifiedConformalInference (DoubledSpace H))
            variable (hA : IsGOne (doubledSpaceCl11Action (E := H)) CIK.A)
            variable (hAMP : IsGNegOne (doubledSpaceCl11Action (E := H)) CIK.A_MP)
            variable (hAD : IsGNegOne (doubledSpaceCl11Action (E := H)) CIK.A_D)
            variable (hA' : IsGOne (doubledSpaceCl11Action (E := H)) CCI.A)
            variable (hAMP' : IsGNegOne (doubledSpaceCl11Action (E := H)) CCI.A_MP)
            variable (R : PolarizedRecompositionData H α βplus βminus)

            example :
                IsGZero (doubledSpaceCl11Action (E := H)) CIK.mpChiralGap
                  ∧ IsGZero (doubledSpaceCl11Action (E := H)) CIK.dilationGap
                  ∧ IsGZero (doubledSpaceCl11Action (E := H)) CIK.drazinCoreProj
                  ∧ IsGZero (doubledSpaceCl11Action (E := H))
                      (chiralGrading CCI.toConformalInference)
                  ∧ R.couplingLogDefect
                      = PolarizedRecompositionData.generalizedMetricTwistShadow R :=
              correctedOwner_trunk_outputs (H := H) (CIK := CIK) (CCI := CCI)
                hA hAMP hAD hA' hAMP' R

            example :
                TrunkOutputs H α βplus βminus CIK CCI R :=
              correctedOwner_trunk_outputs_struct (H := H) (CIK := CIK) (CCI := CCI)
                hA hAMP hAD hA' hAMP' R

            end TrunkOutputs

            end Scratch.PhaseSpaceCausalFlowBridge
            """
        )
        if proc.returncode != 0:
            raise AssertionError(_combined_output(proc))


if __name__ == "__main__":
    unittest.main()
