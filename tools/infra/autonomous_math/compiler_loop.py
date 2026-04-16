#!/usr/bin/env python3
"""Compiler/proof repair loop surface."""

from __future__ import annotations

import subprocess
from dataclasses import dataclass
from pathlib import Path
from typing import Any


@dataclass
class CompileResult:
    ok: bool
    statement_invalid: bool
    feedback: str
    command: list[str]


def close(file_path: Path, repo_root: Path) -> CompileResult:
    cmd = ["lake", "env", "lean", str(file_path)]
    proc = subprocess.run(cmd, cwd=repo_root, capture_output=True, text=True, check=False)
    stderr = (proc.stderr or "").strip()
    stdout = (proc.stdout or "").strip()
    feedback = (stderr + "\n" + stdout).strip()[-8000:]
    ok = proc.returncode == 0
    return CompileResult(
        ok=ok,
        statement_invalid=(not ok),
        feedback=feedback,
        command=cmd,
    )

