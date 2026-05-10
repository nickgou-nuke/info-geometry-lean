from __future__ import annotations

import ast
import py_compile
import subprocess
from pathlib import Path


REPO = Path(__file__).resolve().parents[1]
EXCLUDED_PREFIXES = (
    ".lake/",
    ".venv/",
    ".venv-py312/",
    "venv/",
    "external/",
    "external_refs/",
    "artifacts/",
    "archive/",
)
LEGACY_TOOL_SCRIPTS = [
    Path("tools/find_scc.py"),
    Path("tools/list_collections.py"),
    Path("tools/query_arango.py"),
    Path("tools/query_dag.py"),
    Path("tools/refactor_namespaces.py"),
    Path("tools/run_arango_query.py"),
    Path("tools/run_arango_query2.py"),
]


def repository_python_files() -> list[Path]:
    tracked = subprocess.check_output(["git", "ls-files", "*.py"], cwd=REPO, text=True).splitlines()
    untracked = subprocess.check_output(
        ["git", "ls-files", "--others", "--exclude-standard", "*.py"], cwd=REPO, text=True
    ).splitlines()
    paths: list[Path] = []
    for rel in tracked + untracked:
        if rel.startswith(EXCLUDED_PREFIXES):
            continue
        path = REPO / rel
        if path.exists():
            paths.append(path)
    return sorted(set(paths))


def test_repository_python_files_compile() -> None:
    failures: list[str] = []
    for path in repository_python_files():
        try:
            py_compile.compile(str(path), doraise=True)
        except py_compile.PyCompileError as exc:
            failures.append(f"{path.relative_to(REPO)}: {exc.msg}")
    assert failures == []


def test_legacy_tools_are_import_safe_and_main_guarded() -> None:
    """Legacy top-level utilities moved into tools/ must not run queries or rewrites at import time."""
    unsafe: list[str] = []
    for rel in LEGACY_TOOL_SCRIPTS:
        tree = ast.parse((REPO / rel).read_text(encoding="utf-8"), filename=str(rel))
        for node in tree.body:
            if isinstance(node, (ast.Import, ast.ImportFrom, ast.FunctionDef, ast.AsyncFunctionDef, ast.ClassDef)):
                continue
            if isinstance(node, ast.Assign):
                continue
            if isinstance(node, ast.AnnAssign):
                continue
            if isinstance(node, ast.If):
                test = node.test
                is_main_guard = (
                    isinstance(test, ast.Compare)
                    and isinstance(test.left, ast.Name)
                    and test.left.id == "__name__"
                    and any(isinstance(op, ast.Eq) for op in test.ops)
                    and any(isinstance(comp, ast.Constant) and comp.value == "__main__" for comp in test.comparators)
                )
                if is_main_guard:
                    continue
            unsafe.append(f"{rel}:{node.lineno}:{type(node).__name__}")
    assert unsafe == []
