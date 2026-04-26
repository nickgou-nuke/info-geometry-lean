from pathlib import Path
import re
import unittest

REPO = Path(__file__).resolve().parents[1]
CANONICAL = REPO / "lean" / "InfoGeometry" / "Canonical"

SOURIAU_THERMO = CANONICAL / "SouriauThermodynamics.lean"
FORMAL_ROOTS = CANONICAL / "FormalPrimeRootSystem.lean"
THERMAL_EVAL = CANONICAL / "SouriauThermalEvaluation.lean"
PARITY_WITNESS = CANONICAL / "ParityTraceWitness.lean"
PRIME_PARTITIONS = CANONICAL / "PrimeGasPartitions.lean"
DEFORMATION = CANONICAL / "DeformationLayer.lean"


def has_decl(text: str, kind: str, name: str) -> bool:
    if kind in {"def", "abbrev"}:
        pattern = rf"(?m)^\s*(?:noncomputable\s+)?{kind}\s+{re.escape(name)}\b"
    else:
        pattern = rf"(?m)^\s*{kind}\s+{re.escape(name)}\b"
    return re.search(pattern, text) is not None


class SouriauWeylSupertraceLayerTests(unittest.TestCase):
    def test_souriau_thermodynamics_generalized_layer_exists(self) -> None:
        self.assertTrue(SOURIAU_THERMO.exists(), f"missing file: {SOURIAU_THERMO}")
        text = SOURIAU_THERMO.read_text()
        self.assertTrue(has_decl(text, "structure", "GeneralizedSouriauTemperature"))
        self.assertTrue(has_decl(text, "structure", "ClassicalMomentMap"))
        self.assertTrue(has_decl(text, "def", "classicalThermalHamiltonian"))
        self.assertTrue(has_decl(text, "def", "classicalGibbsWeight"))
        self.assertTrue(has_decl(text, "structure", "QuantumRepresentationLayer"))
        self.assertTrue(has_decl(text, "def", "quantumPartitionFunction"))
        self.assertTrue(has_decl(text, "structure", "WeightDecompositionWitness"))
        self.assertTrue(has_decl(text, "def", "quantumCharacterIfWeighted"))

    def test_formal_prime_root_system_exists(self) -> None:
        self.assertTrue(FORMAL_ROOTS.exists(), f"missing file: {FORMAL_ROOTS}")
        text = FORMAL_ROOTS.read_text()
        self.assertIn("namespace InfoGeometry.Canonical.FormalPrimeRootSystem", text)
        self.assertTrue(has_decl(text, "structure", "FinitePrimeSet"))
        self.assertTrue(has_decl(text, "def", "FormalPrimeRootLattice"))
        self.assertTrue(has_decl(text, "def", "BooleanWeylGroup"))
        self.assertTrue(has_decl(text, "def", "weylSign"))
        self.assertTrue(has_decl(text, "def", "rho_P"))
        self.assertTrue(has_decl(text, "theorem", "finite_denominator_identity"))

    def test_souriau_thermal_evaluation_exists(self) -> None:
        self.assertTrue(THERMAL_EVAL.exists(), f"missing file: {THERMAL_EVAL}")
        text = THERMAL_EVAL.read_text()
        self.assertIn("namespace InfoGeometry.Canonical.SouriauThermalEvaluation", text)
        self.assertTrue(has_decl(text, "def", "rootThermalEvaluation"))
        self.assertTrue(has_decl(text, "def", "finiteParityProduct"))
        self.assertTrue(has_decl(text, "def", "finiteParitySubsetSum"))
        self.assertTrue(has_decl(text, "theorem", "finite_euler_weyl_identity"))

    def test_parity_trace_witness_exists(self) -> None:
        self.assertTrue(PARITY_WITNESS.exists(), f"missing file: {PARITY_WITNESS}")
        text = PARITY_WITNESS.read_text()
        self.assertIn("namespace InfoGeometry.Canonical.ParityTraceWitness", text)
        self.assertTrue(has_decl(text, "def", "nOfSubset"))
        self.assertTrue(has_decl(text, "theorem", "mobius_on_subset_eq_weyl_sign"))
        self.assertTrue(has_decl(text, "def", "parityCoeff"))
        self.assertTrue(has_decl(text, "def", "fermionCoeff"))
        self.assertTrue(has_decl(text, "theorem", "parityCoeff_eq_mobius"))
        self.assertTrue(has_decl(text, "theorem", "fermionCoeff_eq_absMobius"))

    def test_prime_gas_partitions_exists(self) -> None:
        self.assertTrue(PRIME_PARTITIONS.exists(), f"missing file: {PRIME_PARTITIONS}")
        text = PRIME_PARTITIONS.read_text()
        self.assertIn("namespace InfoGeometry.Canonical.PrimeGasPartitions", text)
        self.assertTrue(has_decl(text, "def", "finiteBosonTrace"))
        self.assertTrue(has_decl(text, "def", "finiteFermionTrace"))
        self.assertTrue(has_decl(text, "def", "finiteParityTrace"))
        self.assertTrue(has_decl(text, "structure", "InfiniteEulerProductConvergenceWitness"))

    def test_deformation_layer_exists(self) -> None:
        self.assertTrue(DEFORMATION.exists(), f"missing file: {DEFORMATION}")
        text = DEFORMATION.read_text()
        self.assertIn("namespace InfoGeometry.Canonical.DeformationLayer", text)
        self.assertTrue(has_decl(text, "structure", "DeformationParameter"))
        self.assertTrue(has_decl(text, "structure", "ThermalEvaluationMap"))
        self.assertTrue(has_decl(text, "structure", "SeparatedDeformationWitness"))
        self.assertTrue(has_decl(text, "theorem", "q_not_identified_with_expNegBeta_without_witness"))


if __name__ == "__main__":
    unittest.main()
