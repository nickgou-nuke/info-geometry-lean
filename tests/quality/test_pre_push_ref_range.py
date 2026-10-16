from __future__ import annotations

import os
import subprocess
import tempfile
import unittest
from pathlib import Path


REPO_ROOT = Path(__file__).resolve().parents[2]
HOOK_SOURCE = REPO_ROOT / ".githooks" / "pre-push"


class PrePushRefRangeTests(unittest.TestCase):
    def setUp(self) -> None:
        self.temp = tempfile.TemporaryDirectory()
        self.repo = Path(self.temp.name)
        subprocess.run(["git", "init", "-q", "-b", "main", str(self.repo)], check=True)
        self.git("config", "user.name", "OpenGauss Hook Test")
        self.git("config", "user.email", "hook-test@example.invalid")

        hook = self.repo / ".githooks" / "pre-push"
        gate = self.repo / "scripts" / "quality" / "post_build_gate.sh"
        owner = self.repo / "lean" / "Owner.lean"
        hook.parent.mkdir(parents=True)
        gate.parent.mkdir(parents=True)
        owner.parent.mkdir(parents=True)
        hook.write_text(HOOK_SOURCE.read_text(encoding="utf-8"), encoding="utf-8")
        (self.repo / ".gitignore").write_text("lean/Temp*.lean\n", encoding="utf-8")
        gate.write_text(
            "#!/usr/bin/env bash\n"
            "set -euo pipefail\n"
            "printf '%s\\n' \"$*\" >> \"$CAPTURE_FILE\"\n",
            encoding="utf-8",
        )
        (self.repo / "lakefile.lean").write_text("-- test project marker\n", encoding="utf-8")
        (self.repo / "lake-manifest.json").write_text("{}\n", encoding="utf-8")
        owner.write_text("-- committed proof source\n", encoding="utf-8")
        (self.repo / "payload.txt").write_text("stage 0\n", encoding="utf-8")
        self.git("add", "-A")
        self.git("commit", "-qm", "stage 0")
        self.base = self.git("rev-parse", "HEAD")

        (self.repo / "payload.txt").write_text("stage 1\n", encoding="utf-8")
        self.git("commit", "-qam", "stage 1")
        self.middle = self.git("rev-parse", "HEAD")

        (self.repo / "payload.txt").write_text("stage 2\n", encoding="utf-8")
        self.git("commit", "-qam", "stage 2")
        self.head = self.git("rev-parse", "HEAD")
        self.zero = "0" * len(self.head)
        self.capture = self.repo / "gate-args.txt"

    def tearDown(self) -> None:
        self.temp.cleanup()

    def git(self, *args: str) -> str:
        result = subprocess.run(
            ["git", *args], cwd=self.repo, check=True, text=True, capture_output=True
        )
        return result.stdout.strip()

    def run_hook(self, updates: str) -> subprocess.CompletedProcess[str]:
        env = os.environ.copy()
        env["CAPTURE_FILE"] = str(self.capture)
        return subprocess.run(
            ["bash", str(self.repo / ".githooks" / "pre-push")],
            cwd=self.repo,
            env=env,
            input=updates,
            text=True,
            capture_output=True,
        )

    def gate_calls(self) -> list[str]:
        if not self.capture.exists():
            return []
        return self.capture.read_text(encoding="utf-8").splitlines()

    def test_checks_every_distinct_remote_base_against_pushed_head(self) -> None:
        updates = (
            f"refs/heads/main {self.head} refs/heads/main {self.middle}\n"
            f"refs/heads/release {self.head} refs/heads/release {self.base}\n"
            f"refs/heads/alias {self.head} refs/heads/alias {self.middle}\n"
        )

        result = self.run_hook(updates)

        self.assertEqual(result.returncode, 0, result.stderr)
        self.assertCountEqual(
            self.gate_calls(),
            [
                f"--incremental --base={self.middle} --head={self.head}",
                f"--incremental --base={self.base} --head={self.head}",
            ],
        )

    def test_new_remote_ref_runs_full_gate(self) -> None:
        self.git("update-ref", "refs/remotes/upstream/main", self.base)
        result = self.run_hook(
            f"refs/heads/new {self.head} refs/heads/new {self.zero}\n"
        )

        self.assertEqual(result.returncode, 0, result.stderr)
        self.assertCountEqual(
            self.gate_calls(),
            [f"--incremental --base={self.base} --head={self.head}", ""],
        )

    def test_mixed_new_and_existing_refs_check_every_base(self) -> None:
        self.git("update-ref", "refs/remotes/upstream/main", self.base)
        updates = (
            f"refs/heads/new {self.head} refs/heads/new {self.zero}\n"
            f"refs/heads/release {self.head} refs/heads/release {self.middle}\n"
        )

        result = self.run_hook(updates)

        self.assertEqual(result.returncode, 0, result.stderr)
        self.assertCountEqual(
            self.gate_calls(),
            [
                f"--incremental --base={self.base} --head={self.head}",
                f"--incremental --base={self.middle} --head={self.head}",
                "",
            ],
        )

    def test_new_remote_ref_without_canonical_base_fails_closed(self) -> None:
        result = self.run_hook(
            f"refs/heads/new {self.head} refs/heads/new {self.zero}\n"
        )

        self.assertNotEqual(result.returncode, 0)
        self.assertIn("without a local upstream/main or origin/main", result.stderr)
        self.assertEqual(self.gate_calls(), [])

    def test_new_remote_ref_runs_nested_source_classifier(self) -> None:
        self.git("update-ref", "refs/remotes/upstream/main", self.base)
        nested = self.repo / "lean_sandbox" / "Sandbox"
        nested.mkdir(parents=True)
        (nested / "Changed.lean").write_text("-- added after canonical base\n", encoding="utf-8")
        actual_gate = self.repo / "scripts" / "quality" / "post_build_gate.sh"
        actual_gate.write_text(
            (REPO_ROOT / "scripts" / "quality" / "post_build_gate.sh").read_text(
                encoding="utf-8"
            ),
            encoding="utf-8",
        )
        self.git("add", "-A")
        self.git("commit", "-qm", "add nested source")
        self.head = self.git("rev-parse", "HEAD")
        self.capture.unlink(missing_ok=True)

        result = self.run_hook(
            f"refs/heads/new {self.head} refs/heads/new {self.zero}\n"
        )

        self.assertNotEqual(result.returncode, 0)
        self.assertIn("outside the package targets routed", result.stderr)
        self.assertIn("lean_sandbox/Sandbox/Changed.lean", result.stderr)
        self.assertEqual(self.gate_calls(), [])

    def test_annotated_tag_is_checked_at_its_peeled_commit(self) -> None:
        self.git("tag", "-a", "release-v1", "-m", "release", self.head)
        tag_object = self.git("rev-parse", "refs/tags/release-v1")
        self.assertNotEqual(tag_object, self.head)
        result = self.run_hook(
            f"refs/tags/release-v1 {tag_object} refs/tags/release-v1 {self.middle}\n"
        )

        self.assertEqual(result.returncode, 0, result.stderr)
        self.assertEqual(
            self.gate_calls(),
            [f"--incremental --base={self.middle} --head={self.head}"],
        )

    def test_deletion_only_push_skips_code_gate(self) -> None:
        result = self.run_hook(
            f"(delete) {self.zero} refs/heads/old {self.base}\n"
        )

        self.assertEqual(result.returncode, 0, result.stderr)
        self.assertEqual(self.gate_calls(), [])

    def test_non_head_commit_is_rejected_before_gate(self) -> None:
        result = self.run_hook(
            f"refs/heads/old {self.middle} refs/heads/old {self.base}\n"
        )

        self.assertNotEqual(result.returncode, 0)
        self.assertIn("the current worktree is at", result.stderr)
        self.assertEqual(self.gate_calls(), [])

    def test_modified_proof_source_is_rejected_before_gate(self) -> None:
        (self.repo / "lean" / "Owner.lean").write_text(
            "-- uncommitted proof source\n", encoding="utf-8"
        )
        result = self.run_hook(
            f"refs/heads/main {self.head} refs/heads/main {self.middle}\n"
        )

        self.assertNotEqual(result.returncode, 0)
        self.assertIn("modified proof/gate sources", result.stderr)
        self.assertEqual(self.gate_calls(), [])

    def test_ignored_lean_source_is_rejected_before_gate(self) -> None:
        injected = self.repo / "lean" / "Injected.lean"
        injected.write_text(
            "-- ignored source that is absent from the pushed tree\n", encoding="utf-8"
        )
        with (self.repo / ".git" / "info" / "exclude").open("a", encoding="utf-8") as exclude:
            exclude.write("lean/Injected.lean\n")
        result = self.run_hook(
            f"refs/heads/main {self.head} refs/heads/main {self.middle}\n"
        )

        self.assertNotEqual(result.returncode, 0)
        self.assertIn("ignored non-scratch Lean sources", result.stderr)
        self.assertIn("lean/Injected.lean", result.stderr)
        self.assertEqual(self.gate_calls(), [])

    def test_repository_ignored_scratch_lean_is_not_treated_as_package_source(self) -> None:
        (self.repo / "lean" / "TempScratch.lean").write_text(
            "-- repository-ignored scratch source\n", encoding="utf-8"
        )
        result = self.run_hook(
            f"refs/heads/main {self.head} refs/heads/main {self.middle}\n"
        )

        self.assertEqual(result.returncode, 0, result.stderr)
        self.assertEqual(
            self.gate_calls(),
            [f"--incremental --base={self.middle} --head={self.head}"],
        )

    def test_nested_temp_name_ignored_by_local_rule_is_still_rejected(self) -> None:
        nested = self.repo / "lean" / "InfoGeometry" / "Foo"
        nested.mkdir(parents=True)
        source = nested / "TempInjected.lean"
        source.write_text("-- ignored nested module\n", encoding="utf-8")
        with (self.repo / ".git" / "info" / "exclude").open("a", encoding="utf-8") as exclude:
            exclude.write("Temp*.lean\n")

        result = self.run_hook(
            f"refs/heads/main {self.head} refs/heads/main {self.middle}\n"
        )

        self.assertNotEqual(result.returncode, 0)
        self.assertIn("ignored non-scratch Lean sources", result.stderr)
        self.assertIn("lean/InfoGeometry/Foo/TempInjected.lean", result.stderr)
        self.assertEqual(self.gate_calls(), [])

    def test_untracked_nested_package_source_is_rejected_before_gate(self) -> None:
        nested = self.repo / "lean_sandbox" / "Sandbox"
        nested.mkdir(parents=True)
        (nested / "Untracked.lean").write_text(
            "-- source outside the pushed tree\n", encoding="utf-8"
        )
        result = self.run_hook(
            f"refs/heads/main {self.head} refs/heads/main {self.middle}\n"
        )

        self.assertNotEqual(result.returncode, 0)
        self.assertIn("untracked proof/gate sources", result.stderr)
        self.assertIn("lean_sandbox/Sandbox/Untracked.lean", result.stderr)
        self.assertEqual(self.gate_calls(), [])

    def test_empty_input_is_a_noop(self) -> None:
        result = self.run_hook("")

        self.assertEqual(result.returncode, 0, result.stderr)
        self.assertIn("no ref updates", result.stdout)
        self.assertEqual(self.gate_calls(), [])

    def test_lakefile_only_diff_runs_umbrella_build(self) -> None:
        with tempfile.TemporaryDirectory() as temp:
            root = Path(temp)
            subprocess.run(["git", "init", "-q", "-b", "main", str(root)], check=True)
            self.git_in(root, "config", "user.name", "OpenGauss Hook Test")
            self.git_in(root, "config", "user.email", "hook-test@example.invalid")

            gate = root / "scripts" / "quality" / "post_build_gate.sh"
            gate.parent.mkdir(parents=True)
            gate.write_text(
                (REPO_ROOT / "scripts" / "quality" / "post_build_gate.sh").read_text(
                    encoding="utf-8"
                ),
                encoding="utf-8",
            )
            lakefile = root / "lakefile.lean"
            lakefile.write_text("-- base config\n", encoding="utf-8")
            self.git_in(root, "add", "-A")
            self.git_in(root, "commit", "-qm", "base config")
            base = self.git_in(root, "rev-parse", "HEAD")

            lakefile.write_text("-- changed config\n", encoding="utf-8")
            self.git_in(root, "commit", "-qam", "change lakefile")

            bin_dir = root / "stub-bin"
            bin_dir.mkdir()
            python_stub = bin_dir / "python3"
            python_stub.write_text(
                "#!/usr/bin/env bash\n"
                "set -euo pipefail\n"
                "printf '%s\\n' \"$*\" >> \"$CAPTURE_FILE\"\n",
                encoding="utf-8",
            )
            python_stub.chmod(0o755)
            capture = root / "commands.txt"
            env = os.environ.copy()
            env["PATH"] = f"{bin_dir}{os.pathsep}{env['PATH']}"
            env["CAPTURE_FILE"] = str(capture)
            result = subprocess.run(
                ["bash", str(gate), "--incremental", f"--base={base}"],
                cwd=root,
                env=env,
                text=True,
                capture_output=True,
            )

            self.assertEqual(result.returncode, 0, result.stdout + result.stderr)
            self.assertIn(
                "tools/infra/run_locked_lake_build.py --wait-for-build-lock InfoGeometry.All",
                capture.read_text(encoding="utf-8"),
            )

    def test_deleted_lean_source_runs_umbrella_build(self) -> None:
        with tempfile.TemporaryDirectory() as temp:
            root = Path(temp)
            subprocess.run(["git", "init", "-q", "-b", "main", str(root)], check=True)
            self.git_in(root, "config", "user.name", "OpenGauss Hook Test")
            self.git_in(root, "config", "user.email", "hook-test@example.invalid")

            gate = root / "scripts" / "quality" / "post_build_gate.sh"
            owner = root / "lean" / "InfoGeometry" / "DeletedOwner.lean"
            gate.parent.mkdir(parents=True)
            owner.parent.mkdir(parents=True)
            gate.write_text(
                (REPO_ROOT / "scripts" / "quality" / "post_build_gate.sh").read_text(
                    encoding="utf-8"
                ),
                encoding="utf-8",
            )
            owner.write_text("-- base owner\n", encoding="utf-8")
            self.git_in(root, "add", "-A")
            self.git_in(root, "commit", "-qm", "base owner")
            base = self.git_in(root, "rev-parse", "HEAD")
            owner.unlink()
            self.git_in(root, "add", "-u")
            self.git_in(root, "commit", "-qm", "delete owner")

            bin_dir = root / "stub-bin"
            bin_dir.mkdir()
            python_stub = bin_dir / "python3"
            python_stub.write_text(
                "#!/usr/bin/env bash\n"
                "set -euo pipefail\n"
                "printf '%s\\n' \"$*\" >> \"$CAPTURE_FILE\"\n",
                encoding="utf-8",
            )
            python_stub.chmod(0o755)
            capture = root / "commands.txt"
            env = os.environ.copy()
            env["PATH"] = f"{bin_dir}{os.pathsep}{env['PATH']}"
            env["CAPTURE_FILE"] = str(capture)
            result = subprocess.run(
                ["bash", str(gate), "--incremental", f"--base={base}"],
                cwd=root,
                env=env,
                text=True,
                capture_output=True,
            )

            self.assertEqual(result.returncode, 0, result.stdout + result.stderr)
            self.assertIn("DeletedOwner.lean", result.stdout)
            self.assertIn(
                "tools/infra/run_locked_lake_build.py --wait-for-build-lock InfoGeometry.All",
                capture.read_text(encoding="utf-8"),
            )

    def test_nested_project_configuration_fails_closed(self) -> None:
        with tempfile.TemporaryDirectory() as temp:
            root = Path(temp)
            subprocess.run(["git", "init", "-q", "-b", "main", str(root)], check=True)
            self.git_in(root, "config", "user.name", "OpenGauss Hook Test")
            self.git_in(root, "config", "user.email", "hook-test@example.invalid")
            gate = root / "scripts" / "quality" / "post_build_gate.sh"
            config = root / "lean_sandbox" / "lakefile.lean"
            gate.parent.mkdir(parents=True)
            config.parent.mkdir(parents=True)
            gate.write_text(
                (REPO_ROOT / "scripts" / "quality" / "post_build_gate.sh").read_text(
                    encoding="utf-8"
                ),
                encoding="utf-8",
            )
            config.write_text("-- base config\n", encoding="utf-8")
            self.git_in(root, "add", "-A")
            self.git_in(root, "commit", "-qm", "base config")
            base = self.git_in(root, "rev-parse", "HEAD")
            config.write_text("-- changed config\n", encoding="utf-8")
            self.git_in(root, "commit", "-qam", "change nested config")

            result = subprocess.run(
                ["bash", str(gate), "--incremental", f"--base={base}"],
                cwd=root,
                text=True,
                capture_output=True,
            )

            self.assertEqual(result.returncode, 2)
            self.assertIn("no package-specific locked build route", result.stderr)
            self.assertIn("lean_sandbox/lakefile.lean", result.stderr)

    def test_nested_project_source_fails_closed(self) -> None:
        with tempfile.TemporaryDirectory() as temp:
            root = Path(temp)
            subprocess.run(["git", "init", "-q", "-b", "main", str(root)], check=True)
            self.git_in(root, "config", "user.name", "OpenGauss Hook Test")
            self.git_in(root, "config", "user.email", "hook-test@example.invalid")
            gate = root / "scripts" / "quality" / "post_build_gate.sh"
            source = root / "lean_sandbox" / "Sandbox" / "Source.lean"
            gate.parent.mkdir(parents=True)
            source.parent.mkdir(parents=True)
            gate.write_text(
                (REPO_ROOT / "scripts" / "quality" / "post_build_gate.sh").read_text(
                    encoding="utf-8"
                ),
                encoding="utf-8",
            )
            source.write_text("-- base source\n", encoding="utf-8")
            self.git_in(root, "add", "-A")
            self.git_in(root, "commit", "-qm", "base source")
            base = self.git_in(root, "rev-parse", "HEAD")
            source.write_text("-- changed source\n", encoding="utf-8")
            self.git_in(root, "commit", "-qam", "change nested source")

            result = subprocess.run(
                ["bash", str(gate), "--incremental", f"--base={base}"],
                cwd=root,
                text=True,
                capture_output=True,
            )

            self.assertEqual(result.returncode, 2)
            self.assertIn("outside the package targets routed", result.stderr)
            self.assertIn("lean_sandbox/Sandbox/Source.lean", result.stderr)

    @staticmethod
    def git_in(cwd: Path, *args: str) -> str:
        result = subprocess.run(
            ["git", *args], cwd=cwd, check=True, text=True, capture_output=True
        )
        return result.stdout.strip()


if __name__ == "__main__":
    unittest.main()
