from pathlib import Path
import os
import re
import subprocess
import unittest


REPO = Path(__file__).resolve().parents[1]
CANONICAL = REPO / "lean" / "InfoGeometry" / "Canonical"
SOURIAU = CANONICAL / "SouriauThermodynamics.lean"
FORMAL_ROOTS = CANONICAL / "FormalPrimeRootSystem.lean"
THERMAL_EVAL = CANONICAL / "SouriauThermalEvaluation.lean"
PARITY = CANONICAL / "ParityTraceWitness.lean"
PARTITIONS = CANONICAL / "PrimeGasPartitions.lean"
DEFORMATION = CANONICAL / "DeformationLayer.lean"
WEYL = CANONICAL / "WeylCharacterEquivalence.lean"
CANONICAL_ALL = CANONICAL / "All.lean"


def has_decl(text: str, kind: str, name: str) -> bool:
    prefix = r"(?:noncomputable\s+)?" if kind in {"def", "abbrev"} else ""
    return re.search(rf"(?m)^\s*{prefix}{kind}\s+{re.escape(name)}\b", text) is not None


class CorrectedSouriauWeylSupertraceTests(unittest.TestCase):
    def test_souriau_quantum_trace_requires_weight_witness_for_character(self) -> None:
        text = SOURIAU.read_text()
        self.assertTrue(has_decl(text, "structure", "GeneralizedSouriauTemperature"))
        self.assertTrue(has_decl(text, "structure", "ClassicalMomentMap"))
        self.assertTrue(has_decl(text, "def", "classicalThermalHamiltonian"))
        self.assertTrue(has_decl(text, "def", "classicalGibbsWeight"))
        self.assertTrue(has_decl(text, "structure", "QuantumRepresentationLayer"))
        self.assertTrue(has_decl(text, "def", "quantumThermalGenerator"))
        self.assertTrue(has_decl(text, "def", "quantumPartitionFunction"))
        self.assertTrue(has_decl(text, "structure", "WeightDecompositionWitness"))
        self.assertTrue(has_decl(text, "def", "quantumCharacterIfWeighted"))
        self.assertIn("traceExists", text)
        self.assertNotIn("quantumPartitionFunction_is_ordinary_Weyl_character", text)

    def test_formal_prime_a1_root_system_and_finite_denominator_exist(self) -> None:
        text = FORMAL_ROOTS.read_text()
        self.assertIn("namespace InfoGeometry.Canonical.FormalPrimeRootSystem", text)
        for name in [
            "FormalPrimeRootLattice",
            "BooleanWeylGroup",
            "PrimeA1RootSystem",
            "rho_P",
        ]:
            self.assertTrue(has_decl(text, "structure" if name != "rho_P" else "def", name), name)
        self.assertTrue(has_decl(text, "def", "weylSign"))
        self.assertTrue(has_decl(text, "def", "weylDenominatorProduct"))
        self.assertTrue(has_decl(text, "def", "weylAlternatingSum"))
        self.assertTrue(has_decl(text, "theorem", "finite_prime_weyl_denominator"))
        self.assertIn("Finset.prod_sub", text)
        forbidden = ["D4", "SO(4,4)", "Klein", "Dirac spectrum"]
        for marker in forbidden:
            self.assertNotIn(marker, text)

    def test_thermal_evaluation_and_partition_traces_are_separate(self) -> None:
        thermal = THERMAL_EVAL.read_text()
        partitions = PARTITIONS.read_text()
        self.assertTrue(has_decl(thermal, "structure", "SouriauThermalEvaluation"))
        self.assertTrue(has_decl(thermal, "theorem", "finite_euler_weyl_identity"))
        self.assertIn("p_neg_beta", thermal)
        for name in ["finiteBosonTrace", "finiteFermionTrace", "finiteParityTrace"]:
            self.assertTrue(has_decl(partitions, "def", name), name)
        self.assertTrue(has_decl(partitions, "structure", "InfiniteEulerProductWitness"))
        self.assertTrue(has_decl(partitions, "theorem", "bosonTrace_eq_zeta"))
        self.assertTrue(has_decl(partitions, "theorem", "fermionTrace_eq_zeta_div_zeta_two_beta"))
        self.assertTrue(has_decl(partitions, "theorem", "parityTrace_eq_inverse_zeta"))
        self.assertIn("zeta", partitions)
        self.assertIn("inverseZeta", partitions)

    def test_parity_witness_keeps_mobius_zero_separate_from_weyl_sign(self) -> None:
        text = PARITY.read_text()
        self.assertTrue(has_decl(text, "def", "squarefreeIntegerOfSubset"))
        self.assertTrue(has_decl(text, "def", "parityCoeff"))
        self.assertTrue(has_decl(text, "def", "fermionCoeff"))
        self.assertTrue(has_decl(text, "theorem", "mobius_squarefree_subset_eq_weyl_sign"))
        self.assertTrue(has_decl(text, "theorem", "nonsquarefree_not_represented_by_boolean_prime_state"))
        self.assertTrue(has_decl(text, "theorem", "parityCoeff_eq_mobius"))
        self.assertTrue(has_decl(text, "theorem", "fermionCoeff_eq_abs_mobius"))
        self.assertIn("absence", text)

    def test_deformation_layer_quarantines_q_character_claims(self) -> None:
        text = DEFORMATION.read_text()
        self.assertTrue(has_decl(text, "structure", "DeformationParameterWitness"))
        self.assertTrue(has_decl(text, "structure", "DeformedCharacterWitness"))
        self.assertTrue(has_decl(text, "theorem", "q_identification_requires_witness"))
        self.assertNotIn("q_globally_equals_e_neg_beta", text)
        self.assertNotIn("zeta_is_undeformed_weyl_denominator", text)

    def test_corrected_weyl_character_equivalence_boundary(self) -> None:
        text = WEYL.read_text()
        self.assertIn("inverse zeta", text.lower())
        self.assertIn("parity", text.lower())
        self.assertIn("bosonic", text.lower())
        forbidden = [
            "zeta_is_universe_denominator",
            "zeta_is_undeformed_weyl_denominator",
            "unconditional_zeta_is_weyl_denominator",
        ]
        for marker in forbidden:
            self.assertNotIn(marker, text)

    def test_canonical_all_imports_corrected_supertrace_layer(self) -> None:
        text = CANONICAL_ALL.read_text()
        for module in [
            "FormalPrimeRootSystem",
            "SouriauThermalEvaluation",
            "ParityTraceWitness",
            "PrimeGasPartitions",
            "DeformationLayer",
            "WeylCharacterEquivalence",
        ]:
            self.assertIn(f"import InfoGeometry.Canonical.{module}", text)

    def test_corrected_supertrace_modules_build(self) -> None:
        env = os.environ.copy()
        env["PATH"] = f"{Path.home() / '.elan' / 'bin'}:{env['PATH']}"
        for module in [
            "InfoGeometry.Canonical.FormalPrimeRootSystem",
            "InfoGeometry.Canonical.SouriauThermalEvaluation",
            "InfoGeometry.Canonical.ParityTraceWitness",
            "InfoGeometry.Canonical.PrimeGasPartitions",
            "InfoGeometry.Canonical.DeformationLayer",
            "InfoGeometry.Canonical.WeylCharacterEquivalence",
        ]:
            subprocess.run(
                ["python3", "tools/infra/run_locked_lake_build.py", "--wait-for-build-lock", module],
                cwd=REPO,
                env=env,
                check=True,
            )


if __name__ == "__main__":
    unittest.main()
