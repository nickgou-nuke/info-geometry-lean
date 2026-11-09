"""Exercise source-lane and audit routing; the subprocess recorder is not Lean."""
from pathlib import Path
import os
import subprocess
import tempfile
import unittest

from tests.quality import test_pre_push_ref_range as push_tests

REPO_ROOT = push_tests.REPO_ROOT


class SourceGuardTests(unittest.TestCase):
    def test_uncommitted_source_lane_is_rejected(self):
        fixture = push_tests.PrePushRefRangeTests()
        fixture.setUp()
        self.addCleanup(fixture.tearDown)
        path = fixture.repo / "src/InfoGeometry/Test.lean"
        path.parent.mkdir(parents=True)
        path.write_text("-- uncommitted source lane\n")
        result = fixture.run_hook(f"refs/heads/main {fixture.head} refs/heads/main {fixture.base}\n")
        self.assertNotEqual(result.returncode, 0)
        self.assertIn("untracked proof/gate sources", result.stderr)
        self.assertEqual(fixture.gate_calls(), [])


class SourceRouteTests(unittest.TestCase):
    def run_route(self, relative, *, delete=False):
        with tempfile.TemporaryDirectory() as temporary:
            root = Path(temporary)
            def git(*args):
                return subprocess.check_output(["git", *args], cwd=root, text=True).strip()
            git("init", "-q", "-b", "main")
            git("config", "user.name", "Gate routing test")
            git("config", "user.email", "gate-test@example.invalid")
            gate = root / "scripts/quality/post_build_gate.sh"
            gate.parent.mkdir(parents=True)
            gate.write_bytes((REPO_ROOT / "scripts/quality/post_build_gate.sh").read_bytes())
            source = root / relative
            source.parent.mkdir(parents=True, exist_ok=True)
            source.write_text("-- initial source\n")
            git("add", ".")
            git("commit", "-qm", "baseline")
            base = git("rev-parse", "HEAD")
            if delete:
                source.unlink()
            else:
                source.write_text("-- changed source\n")
            git("add", "-u")
            git("commit", "-qm", "source change")
            recorder = root / "record-bin/python3"
            recorder.parent.mkdir()
            recorder.write_text('#!/usr/bin/env bash\nprintf "%s\\n" "$*" >> "$ROUTE_CAPTURE"\n')
            recorder.chmod(0o755)
            capture = root / "commands.txt"
            env = dict(os.environ, PATH=str(recorder.parent) + os.pathsep + os.environ["PATH"],
                       ROUTE_CAPTURE=str(capture))
            result = subprocess.run(["bash", str(gate), "--incremental", "--base=" + base],
                                    cwd=root, env=env, text=True, capture_output=True)
            self.assertEqual(result.returncode, 0, result.stdout + result.stderr)
            return capture.read_text().splitlines()

    def test_source_owner_routes_to_separate_lake_lane(self):
        calls = self.run_route("src/InfoGeometry/Quantum/Test.lean")
        self.assertIn("tools/infra/run_locked_lake_build.py --wait-for-build-lock --source-lane InfoGeometry.Quantum.Test", calls)
        self.assertIn("tools/infra/axiom_audit.py --fail-on-gaps src/InfoGeometry/Quantum/Test.lean", calls)

    def test_deleted_source_owner_routes_to_source_umbrella(self):
        calls = self.run_route("src/InfoGeometry/Quantum/Test.lean", delete=True)
        self.assertIn("tools/infra/run_locked_lake_build.py --wait-for-build-lock --source-lane InfoGeometry.All", calls)

    def test_source_lake_configuration_routes_to_source_umbrella(self):
        calls = self.run_route("lakefile.src.lean")
        self.assertIn("tools/infra/run_locked_lake_build.py --wait-for-build-lock --source-lane InfoGeometry.All", calls)

    def test_two_boundary_audit_routes_to_locked_lean(self):
        calls = self.run_route("tools/quality/TwoBoundaryDeclarationAudit.lean")
        self.assertIn("tools/infra/run_locked_lean.py --wait-for-build-lock tools/quality/TwoBoundaryDeclarationAudit.lean", calls)


if __name__ == "__main__":
    unittest.main()
