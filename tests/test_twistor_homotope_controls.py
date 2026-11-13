"""Exercise Twistor control-source binding with isolated Git repositories.

These regressions call only the control fingerprint guard. They do not invoke
the verification driver, Lake, Lean, or any repository build.
"""

from __future__ import annotations

import hashlib
import importlib.util
import os
from pathlib import Path
import re
import subprocess
from types import SimpleNamespace

import pytest


REPO_ROOT = Path(__file__).resolve().parents[1]
VERIFIER_PATH = REPO_ROOT / "verification/twistor-homotope/verify.py"
IMPLEMENTATION_BASE = "c143c264bc18bbf41d692be4e270b5b7f7405702"
REVIEWED_REVISION = "8b270668ea5ce0f0361f606ed09dc94f28922a78"
SCREENER = "tools/infra/opengauss_screener.py"
OTHER_CONTROL = "tools/infra/opengauss_cli.py"
EXPECTED_CONTROLS = {
    "AGENTS.md",
    ".githooks/pre-commit",
    ".githooks/pre-push",
    "lean-toolchain",
    "lake-manifest.json",
    "lakefile.lean",
    "lakefile.toml",
    "pyproject.toml",
    "tools/build_lock.py",
    "tools/infra/build.py",
    SCREENER,
    OTHER_CONTROL,
    "tools/infra/opengauss_ground_truth_contract.py",
    "tools/quality/proof_proxy_staged_gate.py",
    "scripts/vacuity-linter.py",
}
REVIEWED_BYTES = b"reviewed T16 token-boundary correction\n"


@pytest.fixture
def verifier():
    spec = importlib.util.spec_from_file_location("twistor_control_verifier", VERIFIER_PATH)
    assert spec is not None and spec.loader is not None
    module = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(module)
    return module


@pytest.fixture
def control_repo(tmp_path, monkeypatch, verifier):
    # In particular, a test launched by a Git hook must never reuse its parent
    # repository's index, worktree, object database, or configuration.
    for name in (
        "GIT_DIR", "GIT_WORK_TREE", "GIT_INDEX_FILE", "GIT_COMMON_DIR",
        "GIT_OBJECT_DIRECTORY", "GIT_ALTERNATE_OBJECT_DIRECTORIES",
        "GIT_CONFIG", "GIT_CONFIG_PARAMETERS", "GIT_TEMPLATE_DIR",
    ):
        monkeypatch.delenv(name, raising=False)
    monkeypatch.setenv("GIT_CONFIG_NOSYSTEM", "1")
    monkeypatch.setenv("GIT_CONFIG_GLOBAL", os.devnull)
    monkeypatch.setenv("GIT_CONFIG_COUNT", "0")
    for role in ("AUTHOR", "COMMITTER"):
        monkeypatch.setenv(f"GIT_{role}_NAME", "Control Regression")
        monkeypatch.setenv(f"GIT_{role}_EMAIL", "control-regression@example.invalid")

    def git(*args):
        return subprocess.run(
            ["git", "-C", str(tmp_path), *args],
            check=True, text=True, capture_output=True,
        ).stdout.strip()

    def write(path, content):
        destination = tmp_path / path
        destination.parent.mkdir(parents=True, exist_ok=True)
        destination.write_bytes(content)

    def commit(message):
        git("add", "--all")
        git("commit", "-qm", message)
        return git("rev-parse", "HEAD")

    git("init", "-q")
    original = {path: f"base control: {path}\n".encode() for path in EXPECTED_CONTROLS}
    for path, content in original.items():
        write(path, content)
    base = commit("Original frozen controls")
    write(SCREENER, REVIEWED_BYTES)
    reviewed = commit("Reviewed screener migration")

    monkeypatch.setattr(verifier, "ROOT", tmp_path)
    monkeypatch.setattr(verifier, "BASE", base)
    monkeypatch.setattr(verifier, "CONTROLS", sorted(EXPECTED_CONTROLS))
    monkeypatch.setattr(verifier, "CONTROL_SOURCE_REVISIONS", {SCREENER: reviewed})
    return SimpleNamespace(
        guard=verifier, git=git, write=write, commit=commit,
        original=original, base=base, reviewed=reviewed,
    )


def test_production_policy_pins_only_the_reviewed_screener(verifier):
    assert verifier.BASE == IMPLEMENTATION_BASE
    assert verifier.CONTROL_SOURCE_REVISIONS == {SCREENER: REVIEWED_REVISION}
    assert set(verifier.CONTROLS) == EXPECTED_CONTROLS
    assert len(verifier.CONTROLS) == len(EXPECTED_CONTROLS) == 15
    assert "verification/twistor-homotope/verify.py" in verifier.PROTECTED


def test_exact_reviewed_migration_preserves_every_control(control_repo):
    repo = control_repo
    expected = dict(repo.original)
    expected[SCREENER] = REVIEWED_BYTES

    assert repo.git("status", "--porcelain") == ""
    assert repo.guard.control_fingerprints() == {
        path: hashlib.sha256(content).hexdigest() for path, content in expected.items()
    }


def test_unreviewed_committed_screener_change_is_rejected(control_repo):
    repo = control_repo
    repo.write(SCREENER, REVIEWED_BYTES + b"unreviewed change\n")
    repo.commit("Unreviewed screener edit")

    assert repo.git("status", "--porcelain") == ""
    with pytest.raises(RuntimeError, match=re.escape(SCREENER)):
        repo.guard.control_fingerprints()


@pytest.mark.parametrize("path", [SCREENER, OTHER_CONTROL])
def test_dirty_control_worktree_is_rejected(control_repo, path):
    repo = control_repo
    repo.write(path, b"unreviewed control in committed HEAD\n")
    repo.commit("Commit an unreviewed control")
    # The worktree now contains exactly the approved bytes. It must still
    # fail because those bytes are no longer the committed HEAD source.
    repo.write(path, REVIEWED_BYTES if path == SCREENER else repo.original[path])

    assert repo.git("status", "--porcelain")
    with pytest.raises(RuntimeError, match=re.escape(path)):
        repo.guard.control_fingerprints()


def test_committed_unrelated_control_change_is_rejected(control_repo):
    repo = control_repo
    repo.write(OTHER_CONTROL, b"unreviewed change to an unmigrated control\n")
    repo.commit("Alter another frozen control")

    assert repo.git("status", "--porcelain") == ""
    with pytest.raises(RuntimeError, match=re.escape(OTHER_CONTROL)):
        repo.guard.control_fingerprints()


def test_missing_pinned_revision_fails_closed(control_repo, monkeypatch):
    repo = control_repo
    missing_revision = "f" * 40
    monkeypatch.setattr(
        repo.guard, "CONTROL_SOURCE_REVISIONS", {SCREENER: missing_revision}
    )

    with pytest.raises(subprocess.CalledProcessError) as error:
        repo.guard.control_fingerprints()
    assert missing_revision + ":" + SCREENER in error.value.cmd


def test_control_mutation_between_fingerprint_captures_is_rejected(control_repo):
    repo = control_repo
    before = repo.guard.control_fingerprints()
    assert before == repo.guard.control_fingerprints()

    repo.write("tools/build_lock.py", b"control changed during verification\n")
    repo.commit("Mutation after initial fingerprint capture")

    with pytest.raises(RuntimeError, match=re.escape("tools/build_lock.py")):
        repo.guard.control_fingerprints()
