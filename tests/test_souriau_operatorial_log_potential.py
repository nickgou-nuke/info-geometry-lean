from pathlib import Path
import subprocess
import unittest


REPO = Path(__file__).resolve().parents[1]
SOURCE = REPO / "lean" / "InfoGeometry" / "Canonical" / "SouriauOperatorialLogPotential.lean"
ALL = REPO / "lean" / "InfoGeometry" / "Canonical" / "All.lean"


class SouriauOperatorialLogPotentialTests(unittest.TestCase):
    def test_source_declares_requested_layers(self) -> None:
        text = SOURCE.read_text(encoding="utf-8")

        for needle in [
            "structure LogRadonNikodymData",
            "structure RegularizedJacobianPotential",
            "structure ModularHamiltonianData",
            "structure OperatorialExponentialFamily",
            "structure DuhamelOperatorDerivative",
            "abbrev DuhamelOperatorialNForms",
            "structure MomentGeneratingReadout",
            "structure SouriauLieThermoData",
            "structure SouriauNegativeLogRNDerivative",
            "abbrev NegativeLogRNDerivative",
            "structure MomentMapGeneratingPotential",
            "structure SouriauKLBregmanWitness",
            "abbrev KLAsBregmanDivergence",
            "structure QuantumOperatorialSouriauFamily",
            "structure RenyiMellinSouriauReadout",
            "structure LieCovarianceAndCocycle",
            "structure SouriauMetriplecticOnsager",
            "structure OptimalTransportWitness",
            "structure GenericMetriplecticCompatibility",
            "structure ConstructiveSouriauTomitaLogPotentialOwner",
            "structure UntracedSouriauOperatorialExponentialFamily",
            "theorem negativeLogDensity_eq_modularHamiltonian",
            "theorem modularHamiltonian_eq_moment_geometricTemperature_constructive",
            "theorem untracedExponential_apply_eq_modular_shift",
            "theorem constructive_operatorial_log_potential_packet",
            "abbrev GENERICCompatibility",
            "theorem KL_eq_expectation_logDensity",
            "theorem KL_eq_neg_expectation_surprisalDensity",
            "theorem negativeLogGibbsDensity_eq_K_beta_add_Phi",
            "theorem modularPotential_eq_K_beta_add_Phi",
            "theorem souriauEntropy_eq_Phi_add_pairing_Q_beta",
            "theorem KL_eq_souriau_Bregman",
            "theorem renyiMellin_eq_temperature_rescaling",
            "theorem renyiLogGenerator_eq_massieu_rescaling_shift",
            "theorem force_eq_variation_of_relativeFreeEnergy",
            "theorem dissipativeFlow_eq_onsager_force",
            "theorem freeEnergyDerivative_nonpos_theorem",
            "theorem relativeEntropy_eq_expectation_difference",
            "theorem entropy_is_expectation_of_modularPotential",
            "theorem dE_eq_zero_and_dS_nonneg",
        ]:
            self.assertIn(needle, text)
        self.assertNotIn("souriauPartitionAtBeta ^ 1", text)
        self.assertIn("souriauPartitionAtBeta ^ gamma", text)

    def test_source_keeps_theorem_honest_boundaries(self) -> None:
        text = SOURCE.read_text(encoding="utf-8")
        self.assertIn("No automatic gravity closure claim", text)
        self.assertIn("No OT theorem without metric witness", text)
        self.assertIn("trace/state/KMS readout", text)
        for forbidden in [
            "negative_log_RN_derivative_eq_entropy_without_expectation",
            "regularized_log_det_eq_entropy",
            "operatorial_exponential_family_eq_scalar_partition_before_trace",
            "souriau_symplectic_implies_wasserstein",
            "renyi_generator_eq_KL_unconditionally",
            "onsager_force_is_physical_force_without_witness",
            "ConstructiveSouriauTomitaLogPotentialOwner where\n  .*Witness : Prop",
            "UntracedSouriauOperatorialExponentialFamily where\n  .*traceClassWitness : Prop",
            "proves quantum gravity",
        ]:
            self.assertNotIn(forbidden, text)

    def test_module_builds_locked(self) -> None:
        result = subprocess.run(
            [
                "python3",
                "tools/infra/run_locked_lake_build.py",
                "--wait-for-build-lock",
                "InfoGeometry.Canonical.SouriauOperatorialLogPotential",
            ],
            cwd=REPO,
            check=False,
            capture_output=True,
            text=True,
        )
        self.assertEqual(result.returncode, 0, result.stdout + result.stderr)

    def test_module_is_imported_in_canonical_all(self) -> None:
        text = ALL.read_text(encoding="utf-8")
        self.assertIn(
            "import InfoGeometry.Canonical.SouriauOperatorialLogPotential",
            text,
        )


if __name__ == "__main__":
    unittest.main()
