#!/usr/bin/env python3
"""Validate the five Nambu/metriplectic owners with unchanged pins and build lock."""
from __future__ import annotations

import argparse
import hashlib
import json
from pathlib import Path
import re
import shutil
import subprocess
import sys

ROOT = Path(__file__).resolve().parents[2]
sys.path.insert(0, str(ROOT))
from tools.quality.reviewed_audit_source import audit_source, parse_audit_output

OWNERS = (
    "InfoGeometry.Algebra.AssociativeNambuScalarReduction",
    "InfoGeometry.Algebra.RealPauliNambuSign",
    "InfoGeometry.Clifford.Cl11MetriplecticPencil",
    "InfoGeometry.Clifford.Cl11EighthRoot",
    "InfoGeometry.Thermo.MatrixGENERICRealization",
)
FOCUSED = ROOT / "verification/real-matrix-split"


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--package-root", type=Path,
                        help="Existing exact-pin dependency directory; use native Lake overrides")
    parser.add_argument("--output-dir", type=Path,
                        default=ROOT / "artifacts/verification/nambu-metriplectic")
    args = parser.parse_args()
    output = args.output_dir.resolve()
    output.mkdir(parents=True, exist_ok=True)
    status_path = output / "status.json"
    status = {"status": "preflight", "scope": list(OWNERS), "commands": []}

    def save_status() -> None:
        status_path.write_text(json.dumps(status, indent=2) + "\n")

    save_status()
    try:
        manifest = json.loads((FOCUSED / "lake-manifest.json").read_text())
        root_manifest = json.loads((ROOT / "lake-manifest.json").read_text())
        root_pins = {p["name"]: p["rev"] for p in root_manifest["packages"]
                     if p["type"] == "git"}
        if (ROOT / "lean-toolchain").read_bytes() != (FOCUSED / "lean-toolchain").read_bytes():
            raise RuntimeError("Focused toolchain differs from root")
        toolchain = (ROOT / "lean-toolchain").read_text().strip()
        pinned = re.fullmatch(r"leanprover/lean4:v(\S+)", toolchain)
        if pinned is None:
            raise RuntimeError(f"Unsupported pinned toolchain syntax: {toolchain}")
        required_version = pinned.group(1)
        lake_version = subprocess.check_output(["lake", "--version"], text=True).strip()
        if re.search(r"\bLean version " + re.escape(required_version) + r"\)", lake_version) is None:
            raise RuntimeError(f"Lake does not report pinned Lean {required_version}: {lake_version}")
        package_root = (args.package_root or ROOT / ".lake/packages").resolve()
        overrides = []
        pins = {}
        for package in manifest["packages"]:
            name, revision = package["name"], package["rev"]
            if root_pins.get(name) != revision:
                raise RuntimeError(f"Focused dependency {name} differs from root")
            directory = package_root / name
            actual = subprocess.check_output(
                ["git", "-C", str(directory), "rev-parse", "HEAD"], text=True).strip()
            if actual != revision:
                raise RuntimeError(f"Dependency {name} differs from its pin")
            relevant = ["*.lean", "lean-toolchain", "lakefile.lean", "lakefile.toml",
                        "lake-manifest.json"]
            dirty = subprocess.check_output(
                ["git", "-C", str(directory), "diff", "HEAD", "--name-only", "--", *relevant],
                text=True)
            untracked = subprocess.check_output(
                ["git", "-C", str(directory), "ls-files", "--others", "--exclude-standard",
                 "--", *relevant], text=True)
            if dirty.strip() or untracked.strip():
                raise RuntimeError(f"Dependency {name} has modified/untracked source")
            pins[name] = revision
            overrides.append({"type": "path", "scope": package.get("scope", ""),
                              "name": name, "dir": str(directory),
                              "inherited": package.get("inherited", False),
                              "manifestFile": package["manifestFile"],
                              "configFile": package["configFile"]})
        options = []
        if args.package_root:
            override_path = output / "package-overrides.json"
            override_path.write_text(json.dumps({"version": manifest["version"],
                                                 "packages": overrides}, indent=2) + "\n")
            options.append(f"--packages={override_path}")
        sources = [ROOT / "lean" / (m.replace(".", "/") + ".lean") for m in OWNERS]

        def hashes() -> dict[str, str]:
            return {str(p.relative_to(ROOT)): hashlib.sha256(p.read_bytes()).hexdigest()
                    for p in sources}

        initial_hashes = hashes()
        for source in sources:
            # Bounded lexical screen; native axiom inspection below decides proof dependencies.
            code = re.sub(r"/-.*?-/", "", source.read_text(), flags=re.S)
            code = re.sub(r"--[^\n]*", "", code)
            if re.search(r"\b(sorry|admit|axiom|native_decide|unsafe|partial)\b", code):
                raise RuntimeError(f"Forbidden proof construct in {source}")

        def run(label: str, arguments: list[str]) -> str:
            command = [sys.executable, str(FOCUSED / "check.py"), *options, *arguments]
            status["status"] = label
            save_status()
            print(f"[{label}] {' '.join(command)}", flush=True)
            chunks = []
            with (output / f"{label}.log").open("w") as log:
                process = subprocess.Popen(command, cwd=ROOT, text=True,
                                           stdout=subprocess.PIPE, stderr=subprocess.STDOUT)
                assert process.stdout is not None
                for line in process.stdout:
                    print(line, end="", flush=True)
                    log.write(line)
                    log.flush()
                    chunks.append(line)
                code = process.wait()
            status["commands"].append({"label": label, "command": command, "exit_code": code})
            save_status()
            if code:
                raise RuntimeError(f"{label} failed with exit {code}")
            return "".join(chunks)

        compiler_log = run("toolchain", ["env", "lean", "--version"])
        compiler_lines = [line for line in compiler_log.splitlines()
                          if line.startswith("Lean (version ")]
        if len(compiler_lines) != 1 or re.match(
                r"Lean \(version " + re.escape(required_version) + r"[,)]", compiler_lines[0]) is None:
            raise RuntimeError(f"Resolved Lean does not match pinned version {required_version}")
        lean_version = compiler_lines[0]
        status.update({"toolchain": toolchain, "lean": lean_version, "lake": lake_version,
                       "lake_executable": shutil.which("lake"),
                       "dependency_pins": pins, "source_sha256_initial": initial_hashes})
        save_status()
        run("build", ["build", *OWNERS])
        for source in sources:
            run(source.stem, ["env", "lean", "-DwarningAsError=true", str(source)])
        audit = output / "OwnedDeclarationsAudit.lean"
        audit.write_text(audit_source(OWNERS))
        native_log = run("axioms", ["env", "lean", "-DwarningAsError=true", str(audit)])
        counts = parse_audit_output(native_log, OWNERS)
        if hashes() != initial_hashes:
            raise RuntimeError("Owned sources changed during verification")
        status.update({"status": "passed", "source_sha256": initial_hashes,
                       "owner_declaration_counts": counts, "dependency_pins": pins,
                       "git_head": subprocess.check_output(
                           ["git", "rev-parse", "HEAD"], cwd=ROOT, text=True).strip(),
                       "coverage": "Five selected owners and their import closure; not root integration"})
        save_status()
        print(f"PASS: {sum(counts.values())} owned declarations audited", flush=True)
        return 0
    except Exception as error:
        status.update({"status": "failed", "error": str(error)})
        save_status()
        raise


if __name__ == "__main__":
    raise SystemExit(main())
