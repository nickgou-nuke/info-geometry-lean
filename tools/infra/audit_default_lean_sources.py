from __future__ import annotations

import argparse
import json
import os
import re
import subprocess
from collections import defaultdict
from pathlib import Path


def imports(path: Path) -> set[str]:
    result = set()
    depth = 0
    with path.open(encoding="utf-8") as source:
        for line in source:
            visible = []
            for token in re.split(r"(/-|-/|--)", line):
                if token == "/-":
                    depth += 1
                elif token == "-/" and depth:
                    depth -= 1
                elif token == "--" and not depth:
                    break
                elif not depth:
                    visible.append(token)
            line = "".join(visible).strip()
            if not line or line in {"module", "prelude"}:
                continue
            match = re.fullmatch(r"(?:(?:public|private)\s+)?import\s+(.+)", line)
            if not match:
                break
            result.update(name.replace("«", "").replace("»", "")
                          for name in match[1].split())
    return result


def closure(roots: set[str], graph: dict[str, set[str]]) -> set[str]:
    seen = set()
    pending = list(roots)
    while pending:
        module = pending.pop()
        if module not in seen:
            seen.add(module)
            pending.extend(graph.get(module, set()) - seen)
    return seen


def default_sources(root: Path) -> dict[str, Path]:
    config = (root / "lakefile.lean").read_text(encoding="utf-8")
    config = re.sub(r"/-.*?-/", "", config, flags=re.S)
    config = re.sub(r"--[^\n]*", "", config)
    result = {}
    blocks = re.finditer(
        r"@\[([^]]*default_target[^]]*)\]\s*lean_lib\s+(\w+)\s+where"
        r"(.*?)(?=^\S|\Z)", config, re.M | re.S)
    for block in blocks:
        body = block[3]
        directory_match = re.search(r'srcDir\s*:=\s*"([^"]+)"', body)
        sub = directory_match.group(1) if directory_match else "."
        # Preserve the lexical path: default-target compatibility symlinks in
        # lean/ must be compared as lean/ paths, not as their proofs/ targets.
        # Normalize `../` in srcDir while preserving symlink identity.
        directory = Path(os.path.normpath(str(root / "lean" / sub)))
        globs = re.search(r"globs\s*:=\s*#\[(.*?)\]", body, re.S)
        if not globs:
            roots = re.search(r"roots\s*:=\s*#\[(.*?)\]", body, re.S)
            if not roots:
                raise ValueError(f"Explicit roots or globs required for default library {block[2]}")
            for root_match in re.finditer(r"`([\w.]+)", roots.group(1)):
                module = root_match.group(1)
                result[module] = directory.joinpath(*module.split(".")).with_suffix(".lean")
            continue
        if re.search(r"\.submodules\s+\.anonymous", globs.group(1)):
            candidates = directory.rglob("*.lean")
            for path in candidates:
                module = ".".join(path.relative_to(directory).with_suffix("").parts)
                result[module] = path
        else:
            for glob in re.finditer(r"(?:(\.andSubmodules|\.submodules)\s+)?`([\w.]+)", globs.group(1)):
                module = glob.group(2)
                base = directory.joinpath(*module.split("."))
                if glob.group(1) != ".submodules":
                    result[module] = base.with_suffix(".lean")
                if glob.group(1):
                    if base.is_dir():
                        for path in base.rglob("*.lean"):
                            name = ".".join(path.relative_to(directory).with_suffix("").parts)
                            result[name] = path
    return result


DEFAULT_WORKSPACE_ROOTS = ("lean", "tests", "proofs", "external")


def audit(root: Path, workspace_roots: tuple[str, ...] | None = None) -> dict:
    if workspace_roots is None:
        workspace_roots = DEFAULT_WORKSPACE_ROOTS
    sources = default_sources(root)
    graph = {module: imports(path) for module, path in sources.items() if path.is_file()}
    reverse = defaultdict(set)
    for module, dependencies in graph.items():
        for dependency in dependencies:
            reverse[dependency].add(module)
    umbrella = {"InfoGeometry.All", "InfoGeometry.AllExhaustive"}
    downstream = closure(umbrella, reverse)
    reachable = closure({"InfoGeometry.All"}, graph)
    tracked = set(subprocess.check_output(
        ["git", "ls-files", "-z"], cwd=root).decode().split("\0"))
    relative = lambda path: str(path.relative_to(root))

    # Filter tracked lean files strictly by configured workspace roots
    repository_sources = sorted(
        path for path in tracked
        if path.endswith(".lean") and any(path.startswith(f"{wr}/") for wr in workspace_roots)
    )
    default_source_paths = {
        relative(path) for path in sources.values() if path.is_file()
    }
    non_default_sources = sorted(
        path for path in repository_sources if path not in default_source_paths
    )
    return {
        "workspace_roots": list(workspace_roots),
        "default_modules": len(sources),
        "repository_lean_files": len(repository_sources),
        "non_default_sources_count": len(non_default_sources),
        "non_default_sources": non_default_sources,
        "missing_sources": sorted(relative(path) for path in sources.values() if not path.is_file()),
        "untracked_sources": sorted(relative(path) for path in sources.values()
                                    if relative(path) not in tracked),
        "missing_from_all": sorted(sources.keys() - reachable - downstream),
        "downstream_of_all": sorted(downstream - umbrella),
    }


def main() -> int:
    parser = argparse.ArgumentParser(description="Audit default Lean targets, Git tracking, and All imports.")
    parser.add_argument("--root", type=Path, default=Path(__file__).resolve().parents[2])
    parser.add_argument("--workspace-roots", nargs="*", default=list(DEFAULT_WORKSPACE_ROOTS),
                        help="Workspace roots to include in audit (default: lean tests proofs external)")
    args = parser.parse_args()
    report = audit(args.root.resolve(), tuple(args.workspace_roots))
    print(json.dumps(report, indent=2))
    return int(any(report[key] for key in
                   ("missing_sources", "untracked_sources", "missing_from_all")))


if __name__ == "__main__":
    raise SystemExit(main())
