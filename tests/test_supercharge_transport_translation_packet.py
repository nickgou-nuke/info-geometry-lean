from pathlib import Path
import subprocess
import tempfile
import textwrap
import unittest


REPO = Path(__file__).resolve().parents[1]
SOURCE = REPO / "lean" / "InfoGeometry" / "Canonical" / "SuperchargeTransportBridge.lean"


def test_supercharge_transport_translation_packet_surface_exists() -> None:
    text = SOURCE.read_text(encoding="utf-8")

    assert "def quasilatticeTranslationCandidate" in text
    assert "def quasilatticeHoppingTranslationCandidate" in text
    assert "def quasilatticeHoppingTranslationSeed" in text
    assert "def quasilatticePhaseLinearTranslationSeed" in text
    assert "def quasilatticePhaseAntilinearTranslationSeed" in text
    assert "theorem quasilatticeTranslationCandidate_eq_hoppingSeed" in text
    assert "theorem quasilatticeTranslationCandidate_eq_phaseLinearSeed_add_phaseAntilinearSeed" in text
    assert "theorem quasilatticeTranslationCandidate_eq_phaseAntilinearSeed_of_commute_phaseLinearPart" in text
    assert "fockAnticommutator (E := E)" in text
    assert "transportCommutator (E := E) V.connectionGenerator (modular_j (E := E))" in text
    assert "spectral_epsilon (E := E)" in text


def _run_snippet(body: str) -> subprocess.CompletedProcess[str]:
    with tempfile.TemporaryDirectory(prefix="supercharge-transport-translation-") as td:
        path = Path(td) / "SuperchargeTransportTranslationSmoke.lean"
        path.write_text(
            textwrap.dedent(
                f"""\
                import InfoGeometry.Canonical.SuperchargeTransportBridge

                open scoped InnerProductSpace
                open InfoGeometry.Krein
                open InfoGeometry.Canonical.BogoliubovTransport
                open InfoGeometry.Canonical.BogoliubovFockSuper
                open InfoGeometry.Canonical.SuperchargeTransportBridge

                namespace Scratch.SuperchargeTransportTranslation

                section

                variable {{E : Type}} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
                local notation "H₂" => DoubledSpace E
                local notation "EndH" => H₂ →L[ℝ] H₂
                variable (V : InfoGeometry.Canonical.BogoliubovVielbein.BogoliubovVielbeinBundle (E := E))

                {body}

                end
                end Scratch.SuperchargeTransportTranslation
                """
            ),
            encoding="utf-8",
        )
        return subprocess.run(
            ["lake", "env", "lean", str(path)],
            cwd=REPO,
            text=True,
            capture_output=True,
        )


class SuperchargeTransportTranslationPacketTests(unittest.TestCase):
    def test_supercharge_transport_translation_packet_module_builds(self) -> None:
        proc = subprocess.run(
            [
                "python3",
                "tools/infra/run_locked_lake_build.py",
                "--wait-for-build-lock",
                "InfoGeometry.Canonical.SuperchargeTransportBridge",
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
