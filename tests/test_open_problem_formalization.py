from pathlib import Path
import os
import re
import subprocess
import unittest


REPO = Path(__file__).resolve().parents[1]
OPEN_PROBLEM = REPO / "lean" / "InfoGeometry" / "Canonical" / "OpenProblemFormalization.lean"
CANONICAL_ALL = REPO / "lean" / "InfoGeometry" / "Canonical" / "All.lean"
SUPER_KMS = REPO / "lean" / "InfoGeometry" / "Canonical" / "SuperKMS_Equilibrium.lean"
CHIRAL_CONES = REPO / "lean" / "InfoGeometry" / "Canonical" / "ChiralRadiationCones.lean"
SOURIAU_THERMO = REPO / "lean" / "InfoGeometry" / "Canonical" / "SouriauThermodynamics.lean"
WEYL_CHARACTER_EQ = REPO / "lean" / "InfoGeometry" / "Canonical" / "WeylCharacterEquivalence.lean"
ANALYTIC_LIMIT = REPO / "lean" / "InfoGeometry" / "Canonical" / "AnalyticLimit.lean"


def has_decl(text: str, kind: str, name: str) -> bool:
    if kind in {"def", "abbrev"}:
        pattern = rf"(?m)^\s*(?:noncomputable\s+)?{kind}\s+{re.escape(name)}\b"
    else:
        pattern = rf"(?m)^\s*{kind}\s+{re.escape(name)}\b"
    return re.search(pattern, text) is not None


class OpenProblemFormalizationTests(unittest.TestCase):
    def test_open_problem_registry_surface_exists(self) -> None:
        self.assertTrue(OPEN_PROBLEM.exists(), f"missing file: {OPEN_PROBLEM}")
        text = OPEN_PROBLEM.read_text()
        self.assertIn("namespace InfoGeometry.Canonical.OpenProblemFormalization", text)
        self.assertIn("import InfoGeometry.Clifford.HestenesDirac", text)
        self.assertTrue(has_decl(text, "structure", "ModularSuperTorus"))
        self.assertTrue(has_decl(text, "structure", "Ternaform"))
        self.assertTrue(has_decl(text, "structure", "SpireStabilityData"))
        self.assertTrue(has_decl(text, "lemma", "self_dual_resonance_lies_on_critical_line"))
        self.assertTrue(has_decl(text, "theorem", "Spire_Stability_Conjecture_typed"))

    def test_all_open_problems_registered_as_explicit_frontier_hypotheses(self) -> None:
        text = OPEN_PROBLEM.read_text()
        expected = [
            "V4_Weyl_Isomorphism",
            "V4_symmetry_forces_compactification",
            "microscopic_V4_induces_partition_modularity",
            "DrazinCore_BPS_Correspondence",
            "DrazinCore_zero_entropy",
            "DiracDrazin_well_posedness",
            "m_eff_anomaly_lock",
            "SouriauDiracDrazin_equivalence",
            "Souriau_KMS_BPS_Correspondence",
            "souriau_equilibrium_implies_riemann_zeros",
            "Ternaform_conformal_closure",
            "ConformalClosure_compact",
            "ternaform_closure_yields_riemann_resonances",
            "Fierz_spacetime_emergence",
            "Fierz_vector_equals_Souriau_temperature",
            "gravity_as_thermal_viscosity",
            "lie_orbit_quantization",
            "spinorial_mellin_transform_has_riemann_spectrum",
            "modular_inversion_forces_critical_line",
            "Riemann_BPS_Correspondence",
            "MaxEnt_RH_Equivalence",
            "arithmetic_cosmological_stability",
            "Spire_Stability_Unification",
            "CollisionResistance_RH",
            "identity_preserved",
            "FTA_RH_topological_equivalence",
            "dark_energy_is_modular_remainder",
            "dark_energy_density_scaling",
            "central_charge_calibration",
            "dark_energy_prevents_collision",
            "arithmetic_big_bang_is_bayesian_update",
            "MoebiusV4_dark_matter_dark_energy_swap",
        ]
        missing = [
            name for name in expected
            if re.search(rf"(?m)^\s{{2}}{re.escape(name)}\s*:\s*Prop\b", text) is None
        ]
        self.assertEqual([], missing)
        self.assertNotIn("axiom V4_Weyl_Isomorphism", text)

    def test_canonical_all_imports_open_problem_formalization(self) -> None:
        text = CANONICAL_ALL.read_text()
        self.assertIn("import InfoGeometry.Canonical.OpenProblemFormalization", text)

    def test_open_problem_exposes_concrete_four_by_four_aliases(self) -> None:
        text = OPEN_PROBLEM.read_text()
        self.assertTrue(has_decl(text, "def", "concrete_real_four_by_four_biquaternion_slice"))
        self.assertTrue(has_decl(text, "def", "concrete_majorana_bdg_four_by_four"))
        self.assertTrue(has_decl(text, "def", "concrete_real_pfaffian_bridge"))

    def test_prime_gas_fierz_bridge_is_operatorial_not_scalar_shadow(self) -> None:
        text = OPEN_PROBLEM.read_text()
        self.assertTrue(has_decl(text, "structure", "PrimeGasSymmetry"))
        self.assertTrue(has_decl(text, "structure", "PrimeGasJaynesData"))
        self.assertTrue(has_decl(text, "def", "PrimeGasJaynesConjecture"))
        self.assertTrue(has_decl(text, "structure", "PrimeGasOperatorialFierzPacket"))
        self.assertIn("jaynes : PrimeGasJaynesConjecture gas", text)
        self.assertIn("fierz : FierzStressProjectionContext", text)
        self.assertTrue(has_decl(text, "theorem", "projectedStress_fierz_identity"))
        self.assertTrue(has_decl(text, "theorem", "projectedStress_majorana_identity"))
        self.assertNotIn("spacetime_is_prime_gas_dissipation", text)
        self.assertNotIn("PrimeGasBPSVacuum", text)
        self.assertNotIn("DrazinProjector operatorial_state", text)

    def test_prime_gas_maxent_onsager_bridge_surface_is_explicitly_hypothesis_quarantined(self) -> None:
        text = OPEN_PROBLEM.read_text()
        self.assertTrue(has_decl(text, "structure", "PrimeGasMaxEntPacket"))
        self.assertTrue(has_decl(text, "def", "PrimeGasJaynesRNBridge"))
        self.assertTrue(has_decl(text, "structure", "OnsagerReciprocalFlow"))
        self.assertTrue(has_decl(text, "structure", "PrimeGasOnsagerFierzBridge"))
        self.assertTrue(has_decl(text, "theorem", "onsager_projectedStress_fierz_identity"))
        self.assertIn("eulerProductHypothesis", text)
        self.assertIn("primeLogEnergyHypothesis", text)

    def test_prime_gas_kms_target_bridge_surface_exists(self) -> None:
        text = OPEN_PROBLEM.read_text()
        self.assertTrue(has_decl(text, "structure", "PrimeGasKMSTargetBridge"))
        self.assertTrue(has_decl(text, "def", "toSuperGeometricTemperature"))
        self.assertTrue(has_decl(text, "theorem", "toSuperGeometricTemperature_zero_odd"))
        self.assertTrue(has_decl(text, "theorem", "kms_target_projectedStress_fierz_identity"))
        self.assertIn("betaOdd_eq_zero", text)

    def test_nonequilibrium_b_operator_and_higher_order_onsager_surface_exists(self) -> None:
        text = OPEN_PROBLEM.read_text()
        self.assertTrue(has_decl(text, "structure", "NonEquilibriumSouriauLieThermo"))
        self.assertTrue(has_decl(text, "structure", "ModularDerivationTower"))
        self.assertTrue(has_decl(text, "structure", "BOperatorFormN"))
        self.assertTrue(has_decl(text, "def", "isCompatibleWithModularTower"))
        self.assertTrue(has_decl(text, "structure", "HigherOrderOnsagerOperatorialTheory"))
        self.assertTrue(has_decl(text, "theorem", "higher_order_projectedStress_fierz_identity"))
        self.assertIn("entropyProduction_nonneg", text)
        self.assertIn("maxOrder", text)

    def test_superkms_and_chiral_radiation_cones_surface_exists(self) -> None:
        self.assertTrue(SUPER_KMS.exists(), f"missing file: {SUPER_KMS}")
        self.assertTrue(CHIRAL_CONES.exists(), f"missing file: {CHIRAL_CONES}")

        super_text = SUPER_KMS.read_text()
        chiral_text = CHIRAL_CONES.read_text()
        all_text = CANONICAL_ALL.read_text()

        self.assertIn("namespace InfoGeometry.Canonical.SuperKMS_Equilibrium", super_text)
        self.assertIn("namespace InfoGeometry.Canonical.ChiralRadiationCones", chiral_text)

        self.assertTrue(has_decl(super_text, "structure", "SupergradedAlgebra"))
        self.assertTrue(has_decl(super_text, "structure", "SuperchargeInteractionVertex"))
        self.assertTrue(has_decl(super_text, "structure", "SuperKMSEquilibriumState"))
        self.assertTrue(has_decl(super_text, "theorem", "stimulated_emission_from_ccr"))

        self.assertTrue(has_decl(chiral_text, "structure", "ChiralRadiationCones"))
        self.assertTrue(has_decl(chiral_text, "structure", "ChiralScatteringMass"))
        self.assertTrue(has_decl(chiral_text, "structure", "ConstructiveChiralScatteringMass"))
        self.assertTrue(has_decl(chiral_text, "def", "toChiralScatteringMass"))
        self.assertTrue(has_decl(chiral_text, "theorem", "constructive_mass_eq_flipRate"))
        self.assertTrue(has_decl(chiral_text, "def", "diracMassTerm"))
        self.assertTrue(has_decl(chiral_text, "theorem", "mass_as_chiral_equilibrium_rate"))

        self.assertTrue(has_decl(super_text, "structure", "ConstructiveSuperKMSEquilibriumState"))
        self.assertTrue(has_decl(super_text, "def", "toSuperKMSEquilibriumState"))
        self.assertTrue(has_decl(super_text, "theorem", "constructive_detailed_balance"))

        self.assertIn("import InfoGeometry.Canonical.SuperKMS_Equilibrium", all_text)
        self.assertIn("import InfoGeometry.Canonical.ChiralRadiationCones", all_text)

    def test_souriau_weyl_partition_character_surface_exists(self) -> None:
        self.assertTrue(SOURIAU_THERMO.exists(), f"missing file: {SOURIAU_THERMO}")
        self.assertTrue(WEYL_CHARACTER_EQ.exists(), f"missing file: {WEYL_CHARACTER_EQ}")

        souriau_text = SOURIAU_THERMO.read_text()
        weyl_text = WEYL_CHARACTER_EQ.read_text()
        all_text = CANONICAL_ALL.read_text()

        self.assertIn("namespace InfoGeometry.Canonical.SouriauThermodynamics", souriau_text)
        self.assertIn("namespace InfoGeometry.Canonical.WeylCharacterEquivalence", weyl_text)

        self.assertTrue(has_decl(souriau_text, "structure", "SouriauCartanTemperature"))
        self.assertTrue(has_decl(souriau_text, "def", "souriauPartitionAsCharacter"))
        self.assertTrue(has_decl(souriau_text, "theorem", "souriauPartitionAsCharacter_eq_souriauPartition"))

        self.assertTrue(has_decl(weyl_text, "structure", "WeylDenominatorPrimeModePacket"))
        self.assertTrue(has_decl(weyl_text, "def", "weylDenominatorProduct"))
        self.assertTrue(has_decl(weyl_text, "def", "primeEulerProduct"))
        self.assertTrue(has_decl(weyl_text, "theorem", "weylDenominator_eulerProduct_isomorphic"))
        self.assertTrue(has_decl(weyl_text, "structure", "ParityTraceWitness"))
        self.assertTrue(has_decl(weyl_text, "theorem", "moebius_signature_equivalence"))

        self.assertIn("import InfoGeometry.Canonical.WeylCharacterEquivalence", all_text)

    def test_prime_indexed_zeta_weyl_supertrace_surface_exists(self) -> None:
        self.assertTrue(WEYL_CHARACTER_EQ.exists(), f"missing file: {WEYL_CHARACTER_EQ}")
        weyl_text = WEYL_CHARACTER_EQ.read_text()

        self.assertTrue(has_decl(weyl_text, "structure", "PrimeIndexedSouriauThermalEvaluation"))
        self.assertTrue(has_decl(weyl_text, "def", "inverseZetaAsPrimeIndexedWeylDenominator"))
        self.assertTrue(has_decl(weyl_text, "def", "reciprocalBosonicPartitionFunction"))
        self.assertTrue(has_decl(weyl_text, "theorem", "inverseZeta_eq_primeIndexedWeylDenominator"))
        self.assertTrue(has_decl(weyl_text, "theorem", "inverseZeta_eq_paritySupertrace"))
        self.assertTrue(has_decl(weyl_text, "theorem", "zeta_eq_reciprocalBosonicPartitionFunction"))

    def test_analytic_limit_surface_exists(self) -> None:
        self.assertTrue(ANALYTIC_LIMIT.exists(), f"missing file: {ANALYTIC_LIMIT}")
        text = ANALYTIC_LIMIT.read_text()

        self.assertIn("namespace InfoGeometry.Canonical.AnalyticLimit", text)
        self.assertTrue(has_decl(text, "structure", "FinitePrimeCutoffDirichletData"))
        self.assertTrue(has_decl(text, "def", "finiteInverseZeta"))
        self.assertTrue(has_decl(text, "theorem", "finiteInverseZeta_eq_finiteEulerProduct"))
        self.assertTrue(has_decl(text, "structure", "AnalyticLimitWitness"))
        self.assertTrue(has_decl(text, "theorem", "inverseZeta_eq_tendsto_finiteInverseZeta"))

    def test_open_problem_formalization_builds(self) -> None:
        env = os.environ.copy()
        env["PATH"] = f"{Path.home() / '.elan' / 'bin'}:{env['PATH']}"
        cmd = [
            "python3",
            "tools/infra/run_locked_lake_build.py",
            "--wait-for-build-lock",
            "InfoGeometry.Canonical.OpenProblemFormalization",
        ]
        subprocess.run(cmd, cwd=REPO, env=env, check=True)


if __name__ == "__main__":
    unittest.main()
