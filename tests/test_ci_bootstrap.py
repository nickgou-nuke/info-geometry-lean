"""Bootstrap regressions use isolated temporary Git repositories, never Lake."""
import json
from pathlib import Path
import subprocess
import tempfile
import unittest

from tools.infra.ci_bootstrap import expected_version, verify_version, path_package_report


def git(root, *args):
    return subprocess.run(["git", "-C", str(root), *args], check=True,
                          text=True, capture_output=True).stdout.strip()


def init(root):
    root.mkdir(parents=True, exist_ok=True)
    git(root, "init", "-q")
    git(root, "config", "user.name", "Test")
    git(root, "config", "user.email", "test@example.invalid")
    git(root, "commit", "--allow-empty", "-qm", "fixture")


class VersionTests(unittest.TestCase):
    pin = "leanprover/lean4:v4.34.1\n"

    def test_current_version(self):
        self.assertEqual(verify_version(self.pin, "Lean (version 4.34.1, x86_64, commit abc, Release)"), "4.34.1")

    def test_crlf(self):
        self.assertEqual(expected_version(self.pin.replace("\n", "\r\n")), "4.34.1")

    def test_stale_version_rejected(self):
        with self.assertRaises(ValueError):
            verify_version(self.pin, "Lean (version 4.28.1, Release)")

    def test_prefix_collision_rejected(self):
        with self.assertRaises(ValueError):
            verify_version(self.pin, "Lean (version 4.34.10, Release)")

    def test_release_candidate_rejected_for_stable_pin(self):
        with self.assertRaises(ValueError):
            verify_version(self.pin, "Lean (version 4.34.1-rc1, Release)")

    def test_explicit_release_candidate(self):
        self.assertEqual(verify_version("leanprover/lean4:v4.35.0-rc1", "Lean (version 4.35.0-rc1)"), "4.35.0-rc1")

    def test_bad_pin_and_output(self):
        for pin in ["stable", "leanprover/lean4:nightly", "", "leanprover/lean4:v4.34"]:
            with self.subTest(pin=pin), self.assertRaises(ValueError):
                expected_version(pin)
        for output in ["", "lake 5.0", "warning\nLean (version 4.34.1)"]:
            with self.subTest(output=output), self.assertRaises(ValueError):
                verify_version(self.pin, output)


class PathTests(unittest.TestCase):
    def setUp(self):
        self.tmp = tempfile.TemporaryDirectory()
        self.root = Path(self.tmp.name) / "repo"
        init(self.root)
        self.package = {"name": "Local", "type": "path", "dir": "local", "configFile": "lakefile.toml"}
        self.manifest([self.package])

    def tearDown(self):
        self.tmp.cleanup()

    def manifest(self, packages):
        (self.root / "lake-manifest.json").write_text(json.dumps({"packages": packages}))

    def config(self):
        directory = self.root / "local"
        directory.mkdir(exist_ok=True)
        (directory / "lakefile.toml").write_text('name = "Local"\n')
        return directory

    def row(self):
        return path_package_report(self.root)["packages"][0]

    def test_missing_config_rejected(self):
        self.assertIn("missing_config", self.row()["errors"])

    def test_untracked_directory_is_not_reproducible(self):
        self.config()
        self.assertIn("untracked_path_dependency", self.row()["errors"])

    def test_tracked_config(self):
        self.config()
        git(self.root, "add", "local/lakefile.toml")
        self.assertTrue(self.row()["ok"])

    def test_path_escape_rejected(self):
        self.package["dir"] = "../outside"
        self.manifest([self.package])
        self.assertIn("invalid_path_dependency", self.row()["errors"])

    def test_config_escape_rejected(self):
        self.package["configFile"] = "../lakefile.toml"
        self.manifest([self.package])
        self.assertIn("invalid_path_dependency", self.row()["errors"])

    def test_uninitialized_gitlink(self):
        sha = git(self.root, "rev-parse", "HEAD")
        git(self.root, "update-index", "--add", "--cacheinfo", f"160000,{sha},local")
        self.assertIn("uninitialized_gitlink", self.row()["errors"])

    def test_initialized_gitlink_and_wrong_revision(self):
        directory = self.config()
        init(directory)
        git(directory, "add", "lakefile.toml")
        git(directory, "commit", "-qm", "config")
        sha = git(directory, "rev-parse", "HEAD")
        git(self.root, "update-index", "--add", "--cacheinfo", f"160000,{sha},local")
        self.assertTrue(self.row()["ok"])
        git(directory, "commit", "--allow-empty", "-qm", "later")
        self.assertIn("gitlink_revision_mismatch", self.row()["errors"])

    def test_dirty_gitlink_rejected(self):
        directory = self.config()
        init(directory)
        git(directory, "add", "lakefile.toml")
        git(directory, "commit", "-qm", "config")
        sha = git(directory, "rev-parse", "HEAD")
        git(self.root, "update-index", "--add", "--cacheinfo", f"160000,{sha},local")
        (directory / "lakefile.toml").write_text('name = "Changed"\n')
        self.assertIn("dirty_gitlink", self.row()["errors"])

    def test_all_path_errors_reported(self):
        self.manifest([self.package, {**self.package, "name": "Other", "dir": "other"}])
        report = path_package_report(self.root)
        self.assertEqual(len(report["packages"]), 2)
        self.assertFalse(report["ok"])

    def test_git_dependencies_ignored(self):
        self.manifest([{"name": "mathlib", "type": "git", "rev": "pinned"}])
        self.assertTrue(path_package_report(self.root)["ok"])


if __name__ == "__main__":
    unittest.main()
