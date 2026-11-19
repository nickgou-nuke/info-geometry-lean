from __future__ import annotations

import subprocess
import io
import signal
import tempfile
import unittest
from pathlib import Path
from unittest.mock import Mock, patch

from tools.infra import build, changed_verify, run_full_dag_toolchain
from tools.build_lock import BuildLock, BuildLockBusyError
from tools.infra.run_locked_lake_build import normalize_lake_target, parse_args


class LockedLakeBuildTests(unittest.TestCase):
    def test_build_runs_under_lock_without_implicit_cache_hydration(self):
        state = {"locked": False}

        class Lock:
            lock_path = Path("/tmp/test-build.lock")

            def release(self):
                state["locked"] = False

        def acquire(*args, **kwargs):
            state["locked"] = True
            return Lock()

        with (
            patch.object(build, "repo_root", return_value=Path("/repo")),
            patch.object(build, "acquire_build_lock", side_effect=acquire),
            patch.object(build.subprocess, "Popen", return_value=Mock(wait=Mock(return_value=0))) as popen,
            patch("builtins.print"),
        ):
            self.assertEqual(build.run_locked_lake_build(["-R"]), 0)

        popen.assert_called_once_with(
            ["lake", "build", "-R"], cwd=Path("/repo"), start_new_session=True
        )
        self.assertFalse(state["locked"])

    def test_nested_build_preserves_callers_refresh_lock(self):
        with tempfile.TemporaryDirectory() as directory:
            lock_path = Path(directory) / "build.lock"
            outer_lock = BuildLock(lock_path, "decl-graph-refresh").acquire()
            try:
                with (
                    patch.object(build, "repo_root", return_value=Path("/repo")),
                    patch.object(build, "_validate_lake_workspace_integrity", return_value=None),
                    patch.object(build, "_ensure_mathlib_cache_hydrated"),
                    patch.object(build.subprocess, "Popen", return_value=Mock(wait=Mock(return_value=0))),
                    patch("builtins.print"),
                ):
                    self.assertEqual(
                        build.run_locked_lake_build(
                            ["dagIndexer", "InfoGeometry.Physics.All"],
                            existing_lock=outer_lock,
                        ),
                        0,
                    )

                self.assertEqual(outer_lock._ref_count, 1)
                with self.assertRaises(BuildLockBusyError):
                    BuildLock(lock_path, "concurrent-build", block=False).acquire()
            finally:
                outer_lock.release()

    def test_refresh_prebuild_reuses_existing_lock(self):
        lock = Mock()
        with (
            patch.object(build, "run_locked_lake_build", return_value=0) as run_build,
            patch("builtins.print"),
        ):
            self.assertTrue(
                build.run_locked_prebuild(
                    Path("/repo"), "InfoGeometry.Physics.All", build_lock=lock
                )
            )

        run_build.assert_called_once_with(
            ["dagIndexer", "InfoGeometry.Physics.All"],
            wait_for_lock=False,
            existing_lock=lock,
        )

    def test_lock_file_inode_is_stable_across_release_and_reacquire(self):
        with tempfile.TemporaryDirectory() as directory:
            lock_path = Path(directory) / "build.lock"
            first = BuildLock(lock_path, "first").acquire()
            first_inode = lock_path.stat().st_ino
            first.release()
            self.assertTrue(lock_path.exists())
            second = BuildLock(lock_path, "second", block=False).acquire()
            try:
                self.assertEqual(lock_path.stat().st_ino, first_inode)
            finally:
                second.release()

    def test_busy_lock_reports_metadata_without_claiming_pid_liveness(self):
        with tempfile.TemporaryDirectory() as directory:
            lock_path = Path(directory) / "build.lock"
            first = BuildLock(lock_path, "recorded-owner").acquire()
            try:
                with self.assertRaises(BuildLockBusyError) as error:
                    BuildLock(lock_path, "second", block=False).acquire()
                self.assertEqual(error.exception.metadata["owner"], "recorded-owner")
            finally:
                first.release()

    def test_full_dag_preflight_uses_flock_not_stale_metadata(self):
        with tempfile.TemporaryDirectory() as directory:
            lock_path = Path(directory) / "build.lock"
            with patch.object(run_full_dag_toolchain, "DEFAULT_BUILD_LOCK_PATH", lock_path):
                lock_path.write_text("stale metadata", encoding="utf-8")
                run_full_dag_toolchain.preflight_build_lock_health()
                self.assertEqual(lock_path.read_text(encoding="utf-8"), "")

                holder = BuildLock(lock_path, "test-holder").acquire()
                try:
                    with self.assertRaisesRegex(RuntimeError, "do not remove the lock file"):
                        run_full_dag_toolchain.preflight_build_lock_health()
                finally:
                    holder.release()

    def test_cli_separates_wrapper_options_from_lake_options(self):
        args = parse_args([
            "--wait-for-build-lock", "InfoGeometry.All", "--", "-R"
        ])
        self.assertTrue(args.wait_for_build_lock)
        self.assertEqual(args.targets, ["InfoGeometry.All"])
        self.assertEqual(args.lake_args, ["-R"])

    def test_wrapper_build_flags_and_forwarded_lake_args_compose_exactly(self):
        args = parse_args([
            "--wfail", "InfoGeometry.All", "--", "-R"
        ])
        command = build.lake_build_command(
            [*args.targets, *args.lake_args], wfail=args.wfail
        )
        self.assertEqual(command, ["lake", "build", "--wfail", "InfoGeometry.All", "-R"])

    def test_cli_rejects_wrapper_typo_instead_of_forwarding_it(self):
        with patch("sys.stderr", new=io.StringIO()):
            with self.assertRaises(SystemExit):
                parse_args(["--wait-for-build-lok"])

    def test_no_target_mode_is_incremental_and_preserves_wfail(self):
        args = parse_args(["--wait-for-build-lock", "--wfail"])
        self.assertEqual(args.targets, [])
        self.assertTrue(args.wfail)
        self.assertFalse(args.all_default_targets)

    def test_explicit_default_targets_mode_is_distinct(self):
        args = parse_args(["--wait-for-build-lock", "--all-default-targets"])
        self.assertTrue(args.all_default_targets)
        self.assertEqual(args.targets, [])

    def test_busy_lock_does_not_launch_lake(self):
        busy = build.BuildLockBusyError(Path("/tmp/test-build.lock"), {"pid": 12})
        with (
            patch.object(build, "repo_root", return_value=Path("/repo")),
            patch.object(build, "acquire_build_lock", side_effect=busy),
            patch.object(build.subprocess, "Popen") as popen,
            patch("builtins.print"),
        ):
            self.assertEqual(build.run_locked_lake_build([]), 2)
        popen.assert_not_called()

    def test_lock_acquisition_io_failure_does_not_launch_lake(self):
        with (
            patch.object(build, "repo_root", return_value=Path("/repo")),
            patch.object(build, "acquire_build_lock", side_effect=PermissionError("lock path")),
            patch.object(build.subprocess, "Popen") as popen,
            patch("builtins.print"),
        ):
            self.assertEqual(build.run_locked_lake_build(["InfoGeometry.All"]), 126)
        popen.assert_not_called()

    def test_interrupt_while_waiting_for_lock_returns_130_without_build(self):
        with (
            patch.object(build, "repo_root", return_value=Path("/repo")),
            patch.object(build, "acquire_build_lock", side_effect=KeyboardInterrupt),
            patch.object(build.subprocess, "Popen") as popen,
            patch("builtins.print"),
        ):
            self.assertEqual(build.run_locked_lake_build([], wait_for_lock=True), 130)
        popen.assert_not_called()

    def test_build_launch_failure_releases_lock(self):
        lock = Mock()
        lock.lock_path = Path("/tmp/test-build.lock")
        with (
            patch.object(build, "repo_root", return_value=Path("/repo")),
            patch.object(build, "acquire_build_lock", return_value=lock),
            patch.object(build.subprocess, "Popen", side_effect=FileNotFoundError("lake")),
            patch("builtins.print"),
        ):
            self.assertEqual(build.run_locked_lake_build([]), 127)
        lock.release.assert_called_once()

    def test_release_failure_is_reported_after_successful_build(self):
        lock = Mock()
        lock.lock_path = Path("/tmp/test-build.lock")
        lock.release.side_effect = OSError("unlock failed")
        with (
            patch.object(build, "repo_root", return_value=Path("/repo")),
            patch.object(build, "acquire_build_lock", return_value=lock),
            patch.object(build.subprocess, "Popen", return_value=Mock(wait=Mock(return_value=0))),
            patch("builtins.print"),
        ):
            self.assertEqual(build.run_locked_lake_build([]), 126)

    def test_interrupt_forwards_signal_and_keeps_lock_until_child_exits(self):
        state = {"locked": False, "child_exited": False, "wait_calls": 0}

        class Lock:
            lock_path = Path("/tmp/test-build.lock")

            def release(self):
                self.assert_child_stopped()
                state["locked"] = False

            @staticmethod
            def assert_child_stopped():
                if not state["child_exited"]:
                    raise AssertionError("build lock released while Lake child is alive")

        class Child:
            pid = 4321

            def poll(self):
                return -signal.SIGINT if state["child_exited"] else None

            def wait(self):
                state["wait_calls"] += 1
                if state["wait_calls"] == 1:
                    raise KeyboardInterrupt
                state["child_exited"] = True
                return -signal.SIGINT

        child = Child()

        def acquire(*args, **kwargs):
            state["locked"] = True
            return Lock()

        with (
            patch.object(build, "repo_root", return_value=Path("/repo")),
            patch.object(build, "acquire_build_lock", side_effect=acquire),
            patch.object(build.subprocess, "Popen", return_value=child),
            patch.object(build.os, "killpg") as killpg,
            patch("builtins.print"),
        ):
            self.assertEqual(build.run_locked_lake_build([]), 130)

        killpg.assert_called_once_with(child.pid, signal.SIGINT)
        self.assertEqual(state["wait_calls"], 2)
        self.assertFalse(state["locked"])

    def test_interrupt_forward_failure_still_waits_before_releasing_lock(self):
        state = {"locked": False, "child_exited": False, "wait_calls": 0}

        class Lock:
            lock_path = Path("/tmp/test-build.lock")

            def release(self):
                if not state["child_exited"]:
                    raise AssertionError("build lock released while Lake child is alive")
                state["locked"] = False

        class Child:
            pid = 4322

            def poll(self):
                return -signal.SIGINT if state["child_exited"] else None

            def wait(self):
                if state["wait_calls"] == 0:
                    state["wait_calls"] += 1
                    raise KeyboardInterrupt
                state["child_exited"] = True
                return -signal.SIGINT

        child = Child()

        def acquire(*args, **kwargs):
            state["locked"] = True
            return Lock()

        with (
            patch.object(build, "repo_root", return_value=Path("/repo")),
            patch.object(build, "acquire_build_lock", side_effect=acquire),
            patch.object(build.subprocess, "Popen", return_value=child),
            patch.object(build.os, "killpg", side_effect=PermissionError("denied")),
            patch("builtins.print"),
        ):
            self.assertEqual(build.run_locked_lake_build([]), 130)

        self.assertTrue(state["child_exited"])
        self.assertFalse(state["locked"])

    def test_build_lock_nested_acquisition_refcount(self):
        import tempfile
        from tools.build_lock import BuildLock
        with tempfile.TemporaryDirectory() as tmpdir:
            lock_file = Path(tmpdir) / "test.lock"
            lock = BuildLock(lock_file, "test_owner")
            self.assertEqual(lock._ref_count, 0)
            with lock:
                self.assertEqual(lock._ref_count, 1)
                self.assertIsNotNone(lock._handle)
                with lock:
                    self.assertEqual(lock._ref_count, 2)
                    self.assertIsNotNone(lock._handle)
                self.assertEqual(lock._ref_count, 1)
                self.assertIsNotNone(lock._handle)
            self.assertEqual(lock._ref_count, 0)
            self.assertIsNone(lock._handle)

    def test_normalize_lake_target_maps_lean_paths(self):
        self.assertEqual(
            normalize_lake_target("lean/InfoGeometry/Algebra/Foo.lean"),
            "InfoGeometry.Algebra.Foo",
        )
        self.assertEqual(normalize_lake_target("lean/InfoGeometry.lean"), "InfoGeometry")
        self.assertEqual(normalize_lake_target("tests/InfoGeometryTests.lean"), "InfoGeometryTests")
        self.assertEqual(
            normalize_lake_target("proofs/BogoliubovFrameTransport.lean"),
            "proofs.BogoliubovFrameTransport",
        )
        self.assertEqual(
            normalize_lake_target("src/InfoGeometry/Quantum/Test.lean", source_lane=True),
            "InfoGeometry.Quantum.Test",
        )
        args = parse_args(["--staged", "--wait-for-build-lock"])
        self.assertTrue(args.staged)
        self.assertTrue(args.wait_for_build_lock)

    def test_changed_and_staged_forward_explicit_paths_and_reject_module_names(self):
        import sys
        from tools.infra import run_locked_lake_build as wrapper

        recorded = []
        with patch.object(subprocess, "run", side_effect=lambda cmd, **kw: recorded.append(list(cmd)) or subprocess.CompletedProcess(cmd, 0)):
            with patch.object(sys, "argv", ["run_locked_lake_build.py", "--changed", "lean/InfoGeometry/Foo.lean"]):
                self.assertEqual(wrapper.main(), 0)
            with patch.object(sys, "argv", ["run_locked_lake_build.py", "--staged", "lean/InfoGeometry"]):
                self.assertEqual(wrapper.main(), 0)

        self.assertEqual(recorded[0][-2:], ["--wait-for-build-lock", "lean/InfoGeometry/Foo.lean"] if "--wait-for-build-lock" in recorded[0] else [recorded[0][-2], "lean/InfoGeometry/Foo.lean"])
        self.assertEqual(recorded[0][-1], "lean/InfoGeometry/Foo.lean")
        self.assertIn("--staged-only", recorded[1])
        self.assertEqual(recorded[1][-1], "lean/InfoGeometry")

        with patch("sys.stderr", new=io.StringIO()), patch.object(sys, "argv", ["run_locked_lake_build.py", "--changed", "InfoGeometry.All"]):
            self.assertEqual(wrapper.main(), 2)

    def test_full_dag_run_audit_uses_primary_build_lane(self):
        import sys

        steps: list[tuple[str, str, list[str]]] = []

        def fake_run_step(stage: str, step_name: str, cmd: list[str]) -> None:
            steps.append((stage, step_name, list(cmd)))

        with (
            patch.object(run_full_dag_toolchain, "preflight_build_lock_health"),
            patch.object(run_full_dag_toolchain, "run_step", side_effect=fake_run_step),
            patch.object(run_full_dag_toolchain, "log_spectral_stage"),
            patch.object(sys, "argv", ["run_full_dag_toolchain.py", "--run-audit"]),
        ):
            self.assertEqual(run_full_dag_toolchain.main(), 0)

        audit_steps = [cmd for _, name, cmd in steps if name == "audit-native"]
        self.assertEqual(len(audit_steps), 1)
        cmd = audit_steps[0]
        self.assertIn("AuditNativeRun", cmd)
        self.assertNotIn("--source-lane", cmd)
        self.assertIn("--wait-for-build-lock", cmd)

    def test_changed_verify_skips_redundant_file_gates_by_default(self):
        import sys

        owner = Path("/repo/lean/InfoGeometry/Canonical/Owner.lean")
        with (
            patch.object(changed_verify, "repo_root", return_value=Path("/repo")),
            patch.object(changed_verify, "changed_lean_files", return_value=[owner]),
            patch.object(
                changed_verify,
                "collect_modules",
                return_value=["InfoGeometry.Canonical.Owner"],
            ),
            patch.object(changed_verify, "run_file_gate") as file_gate,
            patch.object(changed_verify, "run_locked_lake_build", return_value=0) as lake_build,
            patch("builtins.print"),
            patch.object(sys, "argv", ["changed_verify.py"]),
        ):
            self.assertEqual(changed_verify.main(), 0)
        file_gate.assert_not_called()
        lake_build.assert_called_once_with(["InfoGeometry.Canonical.Owner"], wait_for_lock=True)

        with (
            patch.object(changed_verify, "repo_root", return_value=Path("/repo")),
            patch.object(changed_verify, "changed_lean_files", return_value=[owner]),
            patch.object(
                changed_verify,
                "collect_modules",
                return_value=["InfoGeometry.Canonical.Owner"],
            ),
            patch.object(changed_verify, "run_file_gate", return_value=0) as file_gate,
            patch.object(changed_verify, "run_locked_lake_build", return_value=0) as lake_build,
            patch("builtins.print"),
            patch.object(sys, "argv", ["changed_verify.py", "--with-file-gates"]),
        ):
            self.assertEqual(changed_verify.main(), 0)
        file_gate.assert_called_once_with(Path("/repo"), owner)
        lake_build.assert_called_once_with(["InfoGeometry.Canonical.Owner"], wait_for_lock=True)


if __name__ == "__main__":
    unittest.main()
