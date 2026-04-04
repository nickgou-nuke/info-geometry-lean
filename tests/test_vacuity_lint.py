import subprocess
import tempfile
import textwrap
import unittest
from pathlib import Path


REPO_ROOT = Path(__file__).resolve().parents[1]


def _run_lint_snippet(body: str) -> subprocess.CompletedProcess[str]:
    with tempfile.TemporaryDirectory(prefix="vacuity-lint-test-") as td:
        path = Path(td) / "LintSmoke.lean"
        path.write_text(
            textwrap.dedent(
                f"""\
                import InfoGeometry.Lint.Vacuity

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


def _combined_output(proc: subprocess.CompletedProcess[str]) -> str:
    return f"{proc.stdout}\n{proc.stderr}"


class VacuityLintTests(unittest.TestCase):
    def test_certified_alias_def_triggers_certification_wash(self):
        proc = _run_lint_snippet(
            """
            def foo : Nat := 1
            def certifiedFoo : Nat := foo
            #lint_vacuity_decl certifiedFoo
            """
        )
        output = _combined_output(proc)
        self.assertEqual(proc.returncode, 0, msg=output)
        self.assertIn("[V5/certification-wash] certifiedFoo", output)

    def test_certified_transport_theorem_triggers_certification_wash(self):
        proc = _run_lint_snippet(
            """
            def foo : Nat := 1
            def certifiedFoo : Nat := foo
            theorem certifiedFoo_eq_foo : certifiedFoo = foo := rfl
            #lint_vacuity_decl certifiedFoo_eq_foo
            """
        )
        output = _combined_output(proc)
        self.assertEqual(proc.returncode, 0, msg=output)
        self.assertIn("[V5/certification-wash] certifiedFoo_eq_foo", output)

    def test_certified_forward_to_certified_target_does_not_trigger_certification_wash(self):
        proc = _run_lint_snippet(
            """
            def certifiedFoo : Nat := 1
            def certifiedBar : Nat := certifiedFoo
            #lint_vacuity_decl certifiedBar
            """
        )
        output = _combined_output(proc)
        self.assertEqual(proc.returncode, 0, msg=output)
        self.assertNotIn("[V5/certification-wash] certifiedBar", output)


if __name__ == "__main__":
    unittest.main()
