from pathlib import Path
import subprocess
import tempfile
import textwrap
import unittest

REPO = Path(__file__).resolve().parents[1]
SOURCE = REPO / "lean" / "InfoGeometry" / "Canonical" / "SplitCliffordHeisenbergAdapter.lean"

def test_split_clifford_heisenberg_adapter_surface_exists() -> None:
    text = SOURCE.read_text(encoding="utf-8")
    assert "structure SplitCliffordCurrentMorphism" in text
    assert "theorem splitCompletion_to_current_morphism :" in text
    assert "Nonempty SplitCliffordCurrentMorphism" in text
    assert "central_commutes" in text
    assert "current_bracket" in text

def _run_snippet(body: str) -> subprocess.CompletedProcess[str]:
    with tempfile.TemporaryDirectory(prefix="split-clifford-heisenberg-") as td:
        path = Path(td) / "SplitCliffordHeisenbergSmoke.lean"
        path.write_text(
            textwrap.dedent(
                f"""\
                import InfoGeometry.Canonical.SplitCliffordHeisenbergAdapter

                open InfoGeometry.Canonical.SplitCliffordHeisenbergAdapter

                namespace Scratch.SplitCliffordHeisenberg

                {body}

                end Scratch.SplitCliffordHeisenberg
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

class SplitCliffordHeisenbergAdapterTests(unittest.TestCase):
    def test_split_clifford_heisenberg_adapter_module_builds(self) -> None:
        proc = subprocess.run(
            [
                "python3",
                "tools/infra/run_locked_lake_build.py",
                "--wait-for-build-lock",
                "InfoGeometry.Canonical.SplitCliffordHeisenbergAdapter",
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
