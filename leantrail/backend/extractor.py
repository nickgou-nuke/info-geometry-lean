from __future__ import annotations

import subprocess
from pathlib import Path


DEFAULT_REFRESH_COMMANDS: tuple[tuple[str, ...], ...] = (
    ("python3", "tools/infra/run_locked_lake_build.py", "InfoGeometry.Audit"),
    ("python3", "tools/infra/refresh_decl_graph.py"),
    ("python3", "tools/infra/refresh_blueprint_tags.py"),
    ("lake", "env", "lean", "--run", "lean/DAG/ProcessFlowExport.lean", "InfoGeometry.Audit", "artifacts/dag/process-flow"),
)


def run_refresh_pipeline(repo_root: Path, commands: tuple[tuple[str, ...], ...] = DEFAULT_REFRESH_COMMANDS) -> None:
    for cmd in commands:
        subprocess.run(cmd, cwd=repo_root, check=True)
