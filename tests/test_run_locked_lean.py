"""Tests for serialized Lean compiler and script invocations."""
from __future__ import annotations

import subprocess
import tempfile
from pathlib import Path
from unittest.mock import patch

import pytest

from tools.infra import run_locked_lean


def test_script_mode_places_run_flag_before_source_file():
    assert run_locked_lean.build_lean_command(
        "/opt/lean/bin/lake", Path("lean/DAG/RawInfoTreeExport.lean"),
        ["lean/DAG/Basic.lean", "/tmp/out"], run_script=True,
    ) == [
        "/opt/lean/bin/lake", "env", "lean", "--run",
        "lean/DAG/RawInfoTreeExport.lean", "lean/DAG/Basic.lean", "/tmp/out",
    ]


def test_timeout_releases_shared_build_lock():
    with tempfile.TemporaryDirectory() as directory:
        root = Path(directory)
        source = root / "Main.lean"
        source.write_text("def main : IO Unit := pure ()\n", encoding="utf-8")
        lock = type("Lock", (), {"release": lambda self: setattr(self, "released", True)})()
        lock.released = False
        with (
            patch.object(run_locked_lean, "_validate_lake_workspace_integrity", return_value=None),
            patch.object(run_locked_lean, "acquire_build_lock", return_value=lock),
            patch.object(run_locked_lean.subprocess, "run",
                         side_effect=subprocess.TimeoutExpired("lake", 1)),
        ):
            with pytest.raises(subprocess.TimeoutExpired):
                run_locked_lean.execute_locked_lean(source, root=root, run_script=True)
        assert lock.released
