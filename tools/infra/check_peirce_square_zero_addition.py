"""Sequential, pinned source check and axiom audit of the Peirce addition."""
from __future__ import annotations
import fcntl
import hashlib
import json
import os
from pathlib import Path
import re
import shutil
import subprocess
import tempfile

TARGETS = [
    "InfoGeometry.Algebra.PeirceRegularityIdentities",
    "InfoGeometry.Singular.MoorePenroseSquareZero",
    "InfoGeometry.Canonical.DrazinShellPeirce",
    "InfoGeometry.Canonical.PeirceSquareZeroExamples",
]


def main() -> None:
    repo = Path.cwd()
    lock = open("/tmp/info-geometry-build.lock", "a", encoding="utf-8")
    fcntl.flock(lock, fcntl.LOCK_EX)
    processes = subprocess.check_output(["ps", "-eo", "pid,comm"], text=True)
    if any(line.split()[-1] in {"lean", "lake", "pytest"}
           for line in processes.splitlines() if line.split()):
        raise RuntimeError("Another compiler or test process is active")
    tmp = Path(os.environ.get("RUNNER_TEMP", tempfile.gettempdir()))
    work = Path(tempfile.mkdtemp(prefix="peirce-mathlib-", dir=tmp))
    out = tmp / "peirce-square-zero-deliverable"
    out.mkdir(exist_ok=True)
    logs: list[str] = []

    def run(*args: str, cwd: Path = repo, verbose: bool = False) -> str:
        result = subprocess.run(args, cwd=cwd, text=True, capture_output=True)
        if verbose or result.returncode:
            text = result.stdout + result.stderr
            logs.append(text)
            (out / "compile.txt").write_text("\n".join(logs), encoding="utf-8")
            print(text, flush=True)
        result.check_returncode()
        return result.stdout

    pin = next(p for p in json.loads((repo / "lake-manifest.json").read_text())[
        "packages"] if p["name"] == "mathlib")
    print("MATHLIB_PIN", pin["rev"], flush=True)
    run("git", "init", str(work))
    run("git", "-C", str(work), "remote", "add", "origin", pin["url"])
    run("git", "-C", str(work), "fetch", "--depth=1", "origin", pin["rev"])
    run("git", "-C", str(work), "checkout", "--detach", "FETCH_HEAD")
    toolchain = (repo / "lean-toolchain").read_text().strip()
    if (work / "lean-toolchain").read_text().strip() != toolchain:
        raise RuntimeError("Toolchain mismatch")
    run("lake", "exe", "cache", "get", cwd=work)
    order: list[tuple[str, Path, Path]] = []
    seen: set[str] = set()

    def visit(module: str) -> None:
        if module in seen:
            return
        seen.add(module)
        relative = Path(*module.split(".")).with_suffix(".lean")
        source = repo / "lean" / relative
        if not source.is_file():
            raise RuntimeError(f"Missing owner: {module}")
        for dep in re.findall(r"^\s*(?:public\s+)?import\s+([\w.]+)",
                              source.read_text(), re.M):
            if not dep.startswith(("Mathlib", "Lean", "Std", "Init", "Batteries")):
                visit(dep)
        order.append((module, relative, source))

    for target in TARGETS:
        visit(target)
    print("OWNER_CLOSURE", [m for m, _, _ in order], flush=True)
    names: list[str] = []
    hashes: dict[str, str] = {}
    for module, relative, source in order:
        text = source.read_text()
        if module in TARGETS:
            if re.search(r"\b(sorry|admit|axiom|native_decide|unsafe)\b", text):
                raise RuntimeError(f"Forbidden proof construct: {module}")
            heads = re.findall(r"^(?:@\[[^\]]*\]\s*)?(?:theorem|lemma|def)\s+(\w+)",
                               text, re.M)
            names.extend(f"{module}.{name}" for name in heads)
            destination = out / "lean" / relative
            destination.parent.mkdir(parents=True, exist_ok=True)
            shutil.copyfile(source, destination)
            hashes[str(Path("lean") / relative)] = hashlib.sha256(source.read_bytes()).hexdigest()
        destination = work / relative
        destination.parent.mkdir(parents=True, exist_ok=True)
        shutil.copyfile(source, destination)
        olean = work / ".lake/build/lib/lean" / relative.with_suffix(".olean")
        olean.parent.mkdir(parents=True, exist_ok=True)
        print("CHECK", module, flush=True)
        run("lake", "env", "lean", "-o", str(olean), str(relative), cwd=work, verbose=True)
    audit = "\n".join([f"import {m}" for m in TARGETS] +
                      [f"#print axioms {name}" for name in names]) + "\n"
    (work / "PeirceAudit.lean").write_text(audit, encoding="utf-8")
    (out / "PeirceAudit.lean").write_text(audit, encoding="utf-8")
    audit_text = run("lake", "env", "lean", "PeirceAudit.lean", cwd=work, verbose=True)
    footprints = re.findall(r"depends on axioms:\s*\[([^\]]*)\]", audit_text, re.S)
    empty = re.findall("does not depend on any axioms", audit_text)
    if len(footprints) + len(empty) != len(names):
        raise RuntimeError("Missing declaration audits")
    for footprint in footprints:
        if not {x.strip() for x in footprint.split(",") if x.strip()} <= {
                "propext", "Classical.choice", "Quot.sound"}:
            raise RuntimeError(f"Unexpected axioms: {footprint}")
    (out / "audit.txt").write_text(audit_text, encoding="utf-8")
    for relative in ["docs/PEIRCE_SQUARE_ZERO_ADDITION.md",
                     "tools/infra/check_peirce_square_zero_addition.py",
                     ".github/workflows/peirce-square-zero.yml"]:
        destination = out / relative
        destination.parent.mkdir(parents=True, exist_ok=True)
        shutil.copyfile(repo / relative, destination)
        hashes[relative] = hashlib.sha256((repo / relative).read_bytes()).hexdigest()
    status = {
        "result": "success", "source_commit": run("git", "rev-parse", "HEAD").strip(),
        "lean_toolchain": toolchain, "mathlib_commit": pin["rev"],
        "compiled_modules": [m for m, _, _ in order], "audited_declarations": names,
        "source_sha256": hashes, "workflow_run": os.environ.get("GITHUB_RUN_ID"),
        "scope": "new modules and unchanged source import closure, not full repository",
    }
    (out / "status.json").write_text(json.dumps(status, indent=2), encoding="utf-8")
    print("AUDITED_DECLARATIONS", len(names), flush=True)


if __name__ == "__main__":
    main()
