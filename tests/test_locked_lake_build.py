from __future__ import annotations

import subprocess
import io
import signal
import tempfile
import unittest
from pathlib import Path
from unittest.mock import Mock, patch

from tools.infra import build
from tools.build_lock import BuildLock, BuildLockBusyError
from tools.infra.run_locked_lake_build import parse_args


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
            patch.object(build, "ensure_mathlib_cache") as prepare,
            patch.object(build.subprocess, "Popen", return_value=Mock(wait=Mock(return_value=0))) as popen,
            patch("builtins.print"),
        ):
            self.assertEqual(build.run_locked_lake_build(["-R"]), 0)

        popen.assert_called_once_with(
            ["lake", "build", "-R"], cwd=Path("/repo"), start_new_session=True
        )
        prepare.assert_not_called()
        self.assertFalse(state["locked"])

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

    def test_busy_lock_skips_cache_preparation(self):
        busy = build.BuildLockBusyError(Path("/tmp/test-build.lock"), {"pid": 12})
        with (
            patch.object(build, "repo_root", return_value=Path("/repo")),
            patch.object(build, "acquire_build_lock", side_effect=busy),
            patch.object(build, "ensure_mathlib_cache") as prepare,
            patch("builtins.print"),
        ):
            self.assertEqual(build.run_locked_lake_build([]), 2)
        prepare.assert_not_called()

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
            patch.object(build, "ensure_mathlib_cache") as prepare,
            patch.object(build.subprocess, "Popen", side_effect=FileNotFoundError("lake")),
            patch("builtins.print"),
        ):
            self.assertEqual(build.run_locked_lake_build([]), 127)
        lock.release.assert_called_once()
        prepare.assert_not_called()

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


if __name__ == "__main__":
    unittest.main()
