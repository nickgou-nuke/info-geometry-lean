from pathlib import Path
import subprocess
import unittest


REPO = Path(__file__).resolve().parents[1]
SOURCE = REPO / "lean" / "InfoGeometry" / "Canonical" / "UnifiedSuperchargeAlgebra.lean"


class DrazinSupergradedTranslationPacketTests(unittest.TestCase):
    def test_drazin_supergraded_translation_packet_surface_exists(self) -> None:
        text = SOURCE.read_text(encoding="utf-8")

        self.assertIn("structure DrazinSupergradedTranslationPacket where", text)
        self.assertIn("noncomputable def drazinTranslationCandidate", text)
        self.assertIn("noncomputable def drazinCentralCandidate", text)
        self.assertIn("noncomputable def drazinDefectCandidate", text)
        self.assertIn("noncomputable def drazinTranslationCentralDefectPacket", text)
        self.assertIn("theorem drazinTranslationCentralDefectPacket_fst", text)
        self.assertIn("theorem drazinTranslationCentralDefectPacket_snd", text)
        self.assertIn("theorem projected_oddOdd_bracket_eq_two_smul_translation_plus_central", text)
        self.assertIn("theorem projected_oddOdd_bracket_eq_two_smul_translation_plus_defect", text)
        self.assertIn("theorem drazinSupergradedTranslationPacket_ofOwners", text)
        self.assertIn("noncomputable def drazinMajoranaConjugateCandidate", text)
        self.assertIn("theorem drazinMajoranaConjugateCandidate_eq_QD_of_commute_chi", text)
        self.assertIn("theorem paired_oddOdd_majoranaBracket_eq_selfBracket_of_commute_chi", text)
        self.assertIn("theorem paired_oddOdd_majoranaBracket_eq_two_smul_translation_plus_central_of_commute_chi", text)
        self.assertIn("theorem paired_oddOdd_majoranaBracket_eq_two_smul_translation_plus_defect_of_commute_chi", text)
        self.assertIn("noncomputable def drazinKramersConjugateCandidate", text)
        self.assertIn("noncomputable def pairedOddOddKramersBracket", text)
        self.assertIn("theorem drazinKramersConjugateCandidate_is_odd_of_commute_GammaS", text)
        self.assertIn("theorem pairedOddOddKramersBracket_eq_ownerReadout", text)
        self.assertIn("canonicalKineticPartK U.kernel", text)
        self.assertIn("InfoGeometry.Canonical.KKTClosure.ZD U.kernel", text)
        self.assertIn("canonicalDefectCentralK U.kernel", text)

    def test_unified_supercharge_algebra_module_builds(self) -> None:
        proc = subprocess.run(
            [
                "python3",
                "tools/infra/run_locked_lake_build.py",
                "--wait-for-build-lock",
                "InfoGeometry.Canonical.UnifiedSuperchargeAlgebra",
            ],
            cwd=REPO,
            text=True,
            capture_output=True,
            env={**__import__("os").environ, "PATH": f"{Path.home() / '.elan' / 'bin'}:{__import__('os').environ.get('PATH', '')}"},
        )
        output = f"{proc.stdout}\n{proc.stderr}"
        self.assertEqual(proc.returncode, 0, msg=output)


if __name__ == "__main__":
    unittest.main()
