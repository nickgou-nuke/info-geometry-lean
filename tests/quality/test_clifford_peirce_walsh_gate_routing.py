"""Exercise the selected package route; the subprocess recorder is not Lean."""
from pathlib import Path
import os
import subprocess
import tempfile
import unittest


REPO_ROOT = Path(__file__).resolve().parents[2]
PACKAGE = "verification/clifford-peirce-walsh"
AUDIT_COMMAND = PACKAGE + "/check.py"


class CliffordPeirceWalshRouteTests(unittest.TestCase):
    def run_route(self, relatives, *, audit_exit=0):
        with tempfile.TemporaryDirectory() as temporary:
            root = Path(temporary)

            def git(*args):
                return subprocess.check_output(
                    ["git", *args], cwd=root, text=True
                ).strip()

            git("init", "-q", "-b", "main")
            git("config", "user.name", "Gate routing test")
            git("config", "user.email", "gate-test@example.invalid")
            gate = root / "scripts/quality/post_build_gate.sh"
            gate.parent.mkdir(parents=True)
            gate.write_bytes((REPO_ROOT / "scripts/quality/post_build_gate.sh").read_bytes())
            for relative in relatives:
                source = root / relative
                source.parent.mkdir(parents=True, exist_ok=True)
                source.write_text("-- initial fixture\n")
            git("add", ".")
            git("commit", "-qm", "baseline")
            base = git("rev-parse", "HEAD")
            for relative in relatives:
                (root / relative).write_text("-- changed fixture\n")
            git("add", "-u")
            git("commit", "-qm", "source change")
            head = git("rev-parse", "HEAD")

            recorder = root / "record-bin/python3"
            recorder.parent.mkdir()
            recorder.write_text(
                '#!/usr/bin/env bash\n'
                'set -euo pipefail\n'
                'printf "%s\\n" "$*" >> "$ROUTE_CAPTURE"\n'
                'if [ "$1" = "verification/clifford-peirce-walsh/check.py" ]; then\n'
                '    exit "$ROUTE_AUDIT_EXIT"\n'
                'fi\n'
                'exit 0\n'
            )
            recorder.chmod(0o755)
            capture = root / "commands.txt"
            env = dict(
                os.environ,
                PATH=str(recorder.parent) + os.pathsep + os.environ["PATH"],
                ROUTE_CAPTURE=str(capture),
                ROUTE_AUDIT_EXIT=str(audit_exit),
            )
            result = subprocess.run(
                ["bash", str(gate), "--incremental", "--base=" + base, "--head=" + head],
                cwd=root, env=env, text=True, capture_output=True,
            )
            calls = capture.read_text().splitlines() if capture.exists() else []
            return result, calls

    def test_each_exact_package_path_invokes_default_audit(self):
        for name in ("lakefile.lean", "lake-manifest.json", "lean-toolchain", "check.py"):
            with self.subTest(name=name):
                result, calls = self.run_route([PACKAGE + "/" + name])
                self.assertEqual(result.returncode, 0, result.stdout + result.stderr)
                self.assertEqual(calls.count(AUDIT_COMMAND), 1)

    def test_package_audit_failure_fails_gate(self):
        result, calls = self.run_route([PACKAGE + "/check.py"], audit_exit=23)
        self.assertEqual(calls.count(AUDIT_COMMAND), 1)
        self.assertEqual(result.returncode, 1, result.stdout + result.stderr)
        self.assertIn("exit code: 23", result.stdout)
        self.assertIn("SOME CHECKS FAILED", result.stdout)

    def test_root_owner_build_and_audits_are_preserved(self):
        result, calls = self.run_route([
            PACKAGE + "/lakefile.lean", "lean/InfoGeometry/Quantum/Test.lean",
        ])
        self.assertEqual(result.returncode, 0, result.stdout + result.stderr)
        self.assertIn(AUDIT_COMMAND, calls)
        self.assertIn(
            "tools/infra/run_locked_lake_build.py --wait-for-build-lock InfoGeometry.Quantum.Test",
            calls,
        )
        self.assertIn(
            "tools/infra/axiom_audit.py --fail-on-gaps lean/InfoGeometry/Quantum/Test.lean",
            calls,
        )
        self.assertIn(
            "tools/quality/semantic_content_audit.py --file-prefix lean --gate", calls,
        )

    def test_root_configuration_still_builds_umbrella(self):
        result, calls = self.run_route([PACKAGE + "/lake-manifest.json", "lakefile.lean"])
        self.assertEqual(result.returncode, 0, result.stdout + result.stderr)
        self.assertIn(AUDIT_COMMAND, calls)
        self.assertIn(
            "tools/infra/run_locked_lake_build.py --wait-for-build-lock InfoGeometry.All", calls,
        )

    def test_other_nested_lean_files_remain_rejected(self):
        for relative in (
            PACKAGE + "/Extra.lean",
            PACKAGE + "/nested/lakefile.lean",
            PACKAGE + "-extra/lakefile.lean",
            "verification/another-package/lakefile.lean",
        ):
            with self.subTest(relative=relative):
                result, calls = self.run_route([PACKAGE + "/check.py", relative])
                self.assertEqual(result.returncode, 2, result.stdout + result.stderr)
                self.assertIn("outside the package targets routed", result.stderr)
                self.assertIn(relative, result.stderr)
                self.assertEqual(calls, [])

    def test_existing_unsupported_package_config_remains_rejected(self):
        relative = "verification/spinorial-core/lake-manifest.json"
        result, calls = self.run_route([PACKAGE + "/check.py", relative])
        self.assertEqual(result.returncode, 2, result.stdout + result.stderr)
        self.assertIn("no package-specific locked build route", result.stderr)
        self.assertIn(relative, result.stderr)
        self.assertEqual(calls, [])

    def test_package_documentation_is_not_a_build_trigger(self):
        result, calls = self.run_route([PACKAGE + "/README.md"])
        self.assertEqual(result.returncode, 0, result.stdout + result.stderr)
        self.assertNotIn(AUDIT_COMMAND, calls)


if __name__ == "__main__":
    unittest.main()
