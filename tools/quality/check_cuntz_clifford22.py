#!/usr/bin/env python3
"""Check byte-identical owners against the immutable Mathlib pin.

The root package contains workstation-only dependencies. A temporary package
avoids changing those dependencies. A mismatched root compiler is reported,
never silently validated by the source check on Mathlib's matching compiler.
"""
from __future__ import annotations
import hashlib
import json
import os
from pathlib import Path
import re
import subprocess
import sys
import tempfile
import urllib.request

ROOT = Path(__file__).resolve().parents[2]
sys.path.insert(0, str(ROOT))
from tools.build_lock import acquire_build_lock  # noqa: E402

TARGET = "InfoGeometry.Algebra.CuntzClifford22Audit"
NEW = {"InfoGeometry.Algebra.CuntzClifford22", "InfoGeometry.Algebra.CuntzClockObstructions", TARGET}
ALLOWED = {"propext", "Quot.sound", "Classical.choice"}


def main() -> None:
    evidence = ROOT / "cuntz-clifford-evidence"
    evidence.mkdir(exist_ok=True)
    metadata = ("lean-toolchain", "lake-manifest.json", "lakefile.lean")
    original = {p: hashlib.sha256((ROOT / p).read_bytes()).hexdigest() for p in metadata}
    manifest = json.loads((ROOT / "lake-manifest.json").read_text())
    pkg = next(p for p in manifest["packages"] if p["name"] == "mathlib")
    rev = pkg["rev"]
    if not re.fullmatch(r"[0-9a-f]{40}", rev):
        raise RuntimeError("An immutable Mathlib commit is required")
    root_compiler = (ROOT / "lean-toolchain").read_text().strip()
    url = f"https://raw.githubusercontent.com/leanprover-community/mathlib4/{rev}/lean-toolchain"
    with urllib.request.urlopen(url, timeout=30) as response:
        compiler = response.read().decode().strip()
    work = Path(tempfile.mkdtemp(prefix="cuntz-clifford22-", dir=os.environ.get("RUNNER_TEMP")))
    (work / "lean-toolchain").write_text(compiler + "\n")
    (work / "lakefile.toml").write_text(
        'name = "cuntz_clifford22_check"\n[[require]]\nname = "mathlib"\n'
        f'git = {json.dumps(pkg["url"])}\nrev = {json.dumps(rev)}\n'
        '[[lean_lib]]\nname = "InfoGeometry"\nsrcDir = "lean"\n')
    sources: dict[str, str] = {}
    order: list[str] = []

    def stage(module: str) -> None:
        if module in sources:
            return
        rel = Path("lean", *module.split(".")).with_suffix(".lean")
        data = (ROOT / rel).read_bytes()
        sources[module] = hashlib.sha256(data).hexdigest()
        dest = work / rel
        dest.parent.mkdir(parents=True, exist_ok=True)
        dest.write_bytes(data)
        for line in re.findall(r"^\s*(?:public\s+)?import\s+([^\n]+)", data.decode(), re.M):
            for dep in line.split("--", 1)[0].split():
                if dep.startswith("InfoGeometry."):
                    stage(dep)
                elif dep.split(".")[0] not in {"Mathlib", "Lean", "Std", "Init", "Batteries", "Aesop", "Qq"}:
                    raise RuntimeError(f"Unsupported dependency {dep}; no stubs are permitted")
        order.append(module)

    stage(TARGET)
    report = {"mathlibRevision": rev, "rootCompiler": root_compiler,
              "checkedCompiler": compiler, "sourceHashes": sources,
              "sourceCheckPassed": False, "axiomAuditPassed": False,
              "rootPackageBuildVerified": False, "scope": "byte-identical narrow owner closure"}
    report_path = evidence / "verification.json"
    report_path.write_text(json.dumps(report, indent=2) + "\n")
    env = dict(os.environ, ELAN_TOOLCHAIN=compiler)
    for key in ("LEAN_PATH", "LEAN_SYSROOT"):
        env.pop(key, None)
    print(json.dumps(report, indent=2), flush=True)
    for executable in ("lean", "lake"):
        if subprocess.run(["pgrep", "-x", executable], stdout=subprocess.DEVNULL).returncode == 0:
            raise RuntimeError(f"Active {executable} process; no concurrent build started")
    lock = acquire_build_lock(None, f"cuntz-clifford22:{os.getpid()}", block=True)
    try:
        subprocess.run(["lake", "exe", "cache", "get"], cwd=work, env=env, check=True)
        subprocess.run(["lake", "env", "lean", "--version"], cwd=work, env=env, check=True)
        audit = ""
        for module in order:
            rel = Path("lean", *module.split(".")).with_suffix(".lean")
            out = work / ".lake/build/lib/lean" / Path(*module.split(".")).with_suffix(".olean")
            out.parent.mkdir(parents=True, exist_ok=True)
            print(f"Checking {module}", flush=True)
            result = subprocess.run(["lake", "env", "lean", "--root=lean", "-o", str(out), str(rel)],
                cwd=work, env=env, text=True, stdout=subprocess.PIPE, stderr=subprocess.STDOUT)
            print(result.stdout, end="", flush=True)
            (evidence / (module + ".log")).write_text(result.stdout)
            result.check_returncode()
            if module in NEW and "warning:" in result.stdout:
                raise RuntimeError(f"New owner has warnings: {module}")
            if module == TARGET:
                audit = result.stdout
        blocks = re.findall(r"depends on axioms:\s*\[([^]]*)\]", audit)
        if len(blocks) < 8 or "sorryAx" in audit:
            raise RuntimeError("Incomplete axiom evidence or an unresolved proof")
        for block in blocks:
            unexpected = {x.strip() for x in block.split(",") if x.strip()} - ALLOWED
            if unexpected:
                raise RuntimeError(f"Unexpected axioms: {unexpected}")
        for module, digest in sources.items():
            rel = Path("lean", *module.split(".")).with_suffix(".lean")
            if hashlib.sha256((ROOT / rel).read_bytes()).hexdigest() != digest:
                raise RuntimeError(f"Source changed during checking: {module}")
        for path, digest in original.items():
            if hashlib.sha256((ROOT / path).read_bytes()).hexdigest() != digest:
                raise RuntimeError(f"Root metadata changed: {path}")
        report.update(sourceCheckPassed=True, axiomAuditPassed=True, auditedDeclarations=len(blocks))
        report_path.write_text(json.dumps(report, indent=2) + "\n")
        print("Narrow source and axiom checks passed; no full-root build is claimed.", flush=True)
    finally:
        lock.release()


if __name__ == "__main__":
    main()
