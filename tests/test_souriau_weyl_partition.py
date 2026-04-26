from pathlib import Path
import os
import re
import subprocess
import unittest


REPO = Path(__file__).resolve().parents[1]
CANONICAL = REPO / "lean" / "InfoGeometry" / "Canonical"
SOURIAU = CANONICAL / "SouriauThermodynamics.lean"
WEYL = CANONICAL / "WeylCharacterEquivalence.lean"
CANONICAL_ALL = CANONICAL / "All.lean"


def has_decl(text: str, kind: str, name: str) -> bool:
    if kind in {"def", "abbrev"}:
        pattern = rf"(?m)^\s*(?:noncomputable\s+)?{kind}\s+{re.escape(name)}\b"
    else:
        pattern = rf"(?m)^\s*{kind}\s+{re.escape(name)}\b"
    return re.search(pattern, text) is not None


class SouriauWeylPartitionTests(unittest.TestCase):
    def test_souriau_temperature_character_surface_exists(self) -> None:
        self.assertTrue(SOURIAU.exists(), f"missing file: {SOURIAU}")
        text = SOURIAU.read_text()
        self.assertIn("namespace InfoGeometry.Canonical.SouriauThermodynamics", text)
        self.assertTrue(has_decl(text, "structure", "CartanSubalgebra"))
        self.assertTrue(has_decl(text, "structure", "SouriauTemperature"))
        self.assertTrue(has_decl(text, "structure", "ThermalRepresentation"))
        self.assertTrue(has_decl(text, "def", "partitionFunction"))
        self.assertTrue(has_decl(text, "theorem", "partitionFunction_eq_character"))
        self.assertIn("cartanCarrier", text)
        self.assertIn("thermalElement", text)
        self.assertIn("character", text)

    def test_weyl_prime_euler_mobius_bridge_is_proof_carrying(self) -> None:
        self.assertTrue(WEYL.exists(), f"missing file: {WEYL}")
        text = WEYL.read_text()
        self.assertIn("namespace InfoGeometry.Canonical.WeylCharacterEquivalence", text)
        self.assertIn("import InfoGeometry.Canonical.SouriauThermodynamics", text)
        self.assertIn("import InfoGeometry.Canonical.PrimeGasMaxEnt", text)
        self.assertTrue(has_decl(text, "structure", "WeylRootSystem"))
        self.assertTrue(has_decl(text, "structure", "PrimeRapidityEncoding"))
        self.assertTrue(has_decl(text, "structure", "WeylDenominatorEulerProductBridge"))
        self.assertTrue(has_decl(text, "structure", "ParityTraceWitness"))
        self.assertTrue(has_decl(text, "theorem", "weylDenominator_eq_primeEulerProduct"))
        self.assertTrue(has_decl(text, "theorem", "mobius_eq_weyl_signature_on_squarefree"))
        self.assertTrue(has_decl(text, "structure", "DeformedSouriauWeylCharacter"))
        self.assertIn("positiveRootToPrime", text)
        self.assertIn("primeRapidity", text)
        self.assertIn("signature_eq_mobius", text)
        self.assertIn("proof-carrying", text)
        forbidden = [
            "RiemannZeta_universe_denominator_theorem",
            "mobius_is_weyl_signature_unconditional",
            "zeta_is_universe_denominator",
            "prove_RH_from_weyl_denominator",
        ]
        for name in forbidden:
            self.assertNotIn(name, text)

    def test_inverse_zeta_and_bosonic_reciprocal_surfaces_exist(self) -> None:
        text = WEYL.read_text()
        self.assertTrue(has_decl(text, "structure", "SouriauThermalPrimeEvaluation"))
        self.assertTrue(has_decl(text, "structure", "InverseZetaWeylParitySupertrace"))
        self.assertTrue(has_decl(text, "theorem", "inverseZeta_eq_weylDenominator_paritySupertrace"))
        self.assertTrue(has_decl(text, "structure", "BosonicZetaPartitionReciprocal"))
        self.assertTrue(has_decl(text, "theorem", "zeta_eq_reciprocal_bosonic_partition"))
        self.assertIn("e_neg_alpha_eq_p_neg_beta", text)
        self.assertIn("inverseZetaValue", text)
        self.assertIn("paritySupertrace", text)
        self.assertIn("bosonicPartition", text)
        self.assertIn("zetaValue", text)
        forbidden = [
            "unconditional_zeta_is_weyl_denominator",
            "zeta_function_is_solved_bosonic_partition",
            "riemann_hypothesis_from_parity_supertrace",
        ]
        for name in forbidden:
            self.assertNotIn(name, text)

    def test_canonical_all_imports_souriau_weyl_partition_layer(self) -> None:
        text = CANONICAL_ALL.read_text()
        self.assertIn("import InfoGeometry.Canonical.SouriauThermodynamics", text)
        self.assertIn("import InfoGeometry.Canonical.WeylCharacterEquivalence", text)

    def test_souriau_weyl_partition_builds(self) -> None:
        env = os.environ.copy()
        env["PATH"] = f"{Path.home() / '.elan' / 'bin'}:{env['PATH']}"
        for module in [
            "InfoGeometry.Canonical.SouriauThermodynamics",
            "InfoGeometry.Canonical.WeylCharacterEquivalence",
        ]:
            cmd = [
                "python3",
                "tools/infra/run_locked_lake_build.py",
                "--wait-for-build-lock",
                module,
            ]
            subprocess.run(cmd, cwd=REPO, env=env, check=True)


if __name__ == "__main__":
    unittest.main()
