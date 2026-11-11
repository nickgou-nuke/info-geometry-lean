#!/usr/bin/env python3
"""Pinned scoped Lake build and fresh owned-declaration audit for Dahm's action.

This checks the canonical repository sources. Existing native and repository
artifacts may be reused by ordinary Lake --rehash. This is not
a fresh build of every dependency, cache reproducibility certification, or the
root project's publication gate. No artifacts are seeded, edited, or deleted.
"""
from __future__ import annotations

import argparse
from collections import Counter
from datetime import datetime, timezone
import hashlib
import json
import os
from pathlib import Path
import re
import shlex
import subprocess
import sys
import time
import tomllib
import traceback
import uuid

PROJECT = Path(__file__).resolve().parent
ROOT = PROJECT.parents[1]
TOOLCHAIN = "leanprover/lean4:v4.34.1"
MATHLIB_REV = "d13f23b723b8a846827a245b89c10fc7d3f11612"
COMPILER_TRACE = "Lean 4.34.1, commit 5045d0056413266e57c625dcd7c365b10e377c52"
PACKAGE = "dahm_klein_validation"
MATHLIB = ROOT / ".lake/packages/mathlib"
NATIVE = MATHLIB / ".lake/packages"
LIB = PROJECT / ".lake/build/lib/lean"
IR = PROJECT / ".lake/build/ir"
PINS = {
    "plausible": "118aa17ee84656b8bd727fef7c458ee8c833385c",
    "LeanSearchClient": "ddf04cf3949fa556442341e87d47f9f6e6074707",
    "importGraph": "e928b72544873815af278d38681b31c0293588e3",
    "proofwidgets": "106ff4fafc74ef4ac99d81dbf3ab399118f497a5",
    "aesop": "355695d523e41d0554926416cba2a2b3544fbbc9",
    "Qq": "6a489d9af5d0c47e5b259e2e8bcdfc1811b5a259",
    "batteries": "f2effa3d803fda822b1f97b806c47cf2adfbcbc2",
    "Cli": "e92c9f15fdfacc8536f31cfb3b7ad26c3c8cd204",
}
EXPLICIT = {
    "PluckerMatrixAction": """coordinatePair coordinates secondCompound
        secondCompound_one secondCompound_mul secondCompoundHom transform
        coordinates_transform transform_one transform_mul transformPoint
        transform_wedge transform_add kleinQ_transform polar_transform
        isKlein_transform isKlein_transform_iff incident_transform_iff""".split(),
    "DahmLineGeometry": """coordinateBasis coordinates_transform_basis
        complementary_pairing_01_23 complementary_pairing_02_31
        complementary_pairing_03_12 not_secondCompound_of_complementary_pairings_ne
        boost det_boost kleinQ_boost kleinQ_boost_of_normalized boost_one_zero
        printed_boost_multiplier_ne_det_at_identity real_klein_split_coordinates
        shear01 shear12 det_shear01 det_shear12 shears_do_not_commute
        exteriorShear01 exteriorShear12 secondCompound_shears_do_not_commute
        kleinQ_shear01 kleinQ_shear12 exists_noncommuting_klein_isometries
        twoPlaneSum kleinQ_twoPlaneSum twoPlaneSum_not_wedge""".split(),
    "ExteriorKleinMatrixAction": """pluckerAction pluckerAction_apply
        pluckerAction_intertwines pluckerAction_pluckerCoords pluckerAction_basis
        standardIndex standardIndex_pair_fst standardIndex_pair_snd
        i4Basis_eq_single pointMatrix pointMatrix_apply pointMatrix_det
        pluckerAction_matrix_apply secondCompound_pointMatrix exteriorPlucker
        exteriorPlucker_kleinQ exteriorPlucker_map exteriorKleinForm_map""".split(),
}
TARGETS = ["InfoGeometry.Projective." + name for name in EXPLICIT]
ALLOWED_AXIOMS = {"propext", "Classical.choice", "Quot.sound"}


def require(condition, message):
    if not condition:
        raise RuntimeError(message)


def digest(path):
    h = hashlib.sha256()
    with Path(path).open("rb") as stream:
        for block in iter(lambda: stream.read(1024 * 1024), b""):
            h.update(block)
    return h.hexdigest()


def write_json(path, data):
    Path(path).write_text(json.dumps(data, indent=2, sort_keys=True) + "\n")


def real_path(path, *, exists=True):
    """Containment is against the checkout, not the smaller scoped package."""
    path = Path(os.path.abspath(path))
    require(path.is_relative_to(ROOT), f"Path outside checkout: {path}")
    for item in (path, *path.parents):
        require(not item.is_symlink(), f"Symlink in verification path: {item}")
        if item == ROOT:
            break
    require(path.resolve() == path, f"Noncanonical path: {path}")
    if exists:
        require(path.exists(), f"Missing required path: {path}")
    return path


def git(directory, *args):
    return subprocess.check_output(
        ["git", "--no-optional-locks", *args], cwd=directory, text=True
    )


def helpers():
    require(PROJECT == ROOT / "verification/dahm-exterior-square",
            "Run the checked-in verification/dahm-exterior-square/check.py")
    sys.path.insert(0, str(ROOT))
    from tools import build_lock
    from tools.infra import build, check_runtime_acceptance, ci_bootstrap
    from tools.quality import reviewed_audit_source, reviewed_native
    result = (build_lock, build, check_runtime_acceptance, ci_bootstrap,
              reviewed_audit_source, reviewed_native)
    for module in result:
        require(real_path(module.__file__).is_relative_to(ROOT / "tools"),
                f"Foreign verification helper: {module.__file__}")
    return result


def identity_snapshot(api, *, sources=False):
    """Reject pin/source-lane drift before allowing Lake to materialize anything."""
    _, build, _, _, _, native_api = api
    for directory in (ROOT, PROJECT, MATHLIB, NATIVE):
        real_path(directory)
        error = build._validate_lake_workspace_integrity(directory)
        require(error is None, error)
    require((ROOT / ".git").is_dir(), "Independent checkout required")
    require(not (PROJECT / ".lake/package-overrides.json").exists(),
            "Scoped package overrides are not part of this source lane")
    root_manifest = json.loads((ROOT / "lake-manifest.json").read_text())
    root_mathlib = [p for p in root_manifest["packages"] if p["name"] == "mathlib"]
    require(len(root_mathlib) == 1 and root_mathlib[0]["type"] == "git"
            and root_mathlib[0]["rev"] == MATHLIB_REV,
            "Root Mathlib pin differs from the reviewed source lane")
    for base in (ROOT, PROJECT, MATHLIB):
        require((base / "lean-toolchain").read_text().strip() == TOOLCHAIN,
                f"Toolchain mismatch: {base}")
    expected_config = {
        "name": PACKAGE, "srcDir": "../../lean",
        "packagesDir": "../../.lake/packages/mathlib/.lake/packages",
        "enableArtifactCache": False, "defaultTargets": TARGETS,
        "require": [{"name": "mathlib", "path": "../../.lake/packages/mathlib"}],
        "lean_lib": [{"name": "InfoGeometry"}, {"name": "DAG"}],
    }
    config = tomllib.loads((PROJECT / "lakefile.toml").read_text())
    require(config == expected_config, "Scoped Lake configuration needs source re-review")
    require(not (PROJECT / "lakefile.lean").exists(), "Ambiguous scoped Lake configuration")
    manifest = json.loads((PROJECT / "lake-manifest.json").read_text())
    require(manifest.get("name") == PACKAGE and manifest.get("lakeDir") == ".lake"
            and manifest.get("version") == "1.2.0"
            and manifest.get("fixedToolchain") is True
            and manifest.get("packagesDir") == config["packagesDir"],
            "Scoped manifest metadata does not match the Lake configuration")
    entries = {p["name"]: p for p in manifest["packages"]}
    require(len(entries) == len(manifest["packages"]) == 9
            and set(entries) == {"mathlib", *PINS}, "Unexpected scoped dependencies")
    expected_mathlib = {
        "name": "mathlib", "type": "path", "dir": "../../.lake/packages/mathlib",
        "scope": "", "inherited": False, "configFile": "lakefile.lean",
        "manifestFile": "lake-manifest.json",
    }
    require(entries["mathlib"] == expected_mathlib, "Unexpected Mathlib path manifest entry")
    native_manifest = json.loads((MATHLIB / "lake-manifest.json").read_text())
    inherited = {p["name"]: p for p in native_manifest["packages"]}
    require(len(inherited) == len(native_manifest["packages"]) == 8
            and set(inherited) == set(PINS)
            and native_manifest["packagesDir"] == ".lake/packages",
            "Unexpected native dependency graph")
    for name, revision in PINS.items():
        entry = inherited[name]
        require(entry["type"] == "git" and entry["rev"] == revision,
                f"Native dependency pin mismatch: {name}")
        require(entries[name] == {**entry, "inherited": True},
                f"Scoped inherited manifest mismatch: {name}")
    packages = {}
    for name, revision, directory in [
        ("mathlib", MATHLIB_REV, MATHLIB),
        *((name, revision, NATIVE / name) for name, revision in PINS.items()),
    ]:
        real_path(directory)
        identity = native_api.checkout_status(directory, revision)
        require(identity.get("clean") is True, f"Unclean or mismatched native checkout: {name}: {identity}")
        packages[name] = {"path": str(directory), "identity": identity}
        if sources:
            inventory = native_api.source_files(directory)
            tracked = set(git(directory, "ls-files", "-z").split("\0"))
            for relative, row in inventory.items():
                if row["link"] is not None:
                    require(relative in tracked and Path(row["resolved"]).is_relative_to(ROOT),
                            f"Unexpected native file alias: {directory / relative}")
                if relative.endswith(".lean"):
                    require(relative in tracked, f"Untracked native Lean source: {directory / relative}")
            packages[name]["sources"] = inventory
    config_paths = [ROOT / p for p in
                    ("lean-toolchain", "lakefile.lean", "lake-manifest.json", ".gitmodules")]
    config_paths += [PROJECT / p for p in
                     ("lean-toolchain", "lakefile.toml", "lake-manifest.json", "check.py")]
    state = {
        "root_head": git(ROOT, "rev-parse", "HEAD").strip(),
        "root_status": git(ROOT, "status", "--porcelain", "--untracked-files=all"),
        "configs": {str(p.relative_to(ROOT)): digest(real_path(p)) for p in config_paths},
        "packages": packages,
    }
    if sources:
        state["repository_sources"] = {
            name: native_api.source_files(ROOT / name,
                  frozenset({".kilo/worktrees"}) if name == "lean" else frozenset())
            for name in ("lean", "tools")
        }
        tracked = set(git(ROOT, "ls-files", "-z").split("\0"))
        for name, inventory in state["repository_sources"].items():
            for relative, row in inventory.items():
                if row["link"] is not None:
                    # Existing unrelated compatibility aliases are bound by the
                    # maintained inventory's link text, resolved path and bytes.
                    require(f"{name}/{relative}" in tracked
                            and Path(row["resolved"]).is_relative_to(ROOT),
                            f"Unexpected repository file alias: {name}/{relative}")
    return state


def artifact_family(module):
    relative = Path(module.replace(".", "/"))
    return sorted({p for base in (LIB, IR)
                   for p in (base / relative.parent).glob(relative.name + ".*")
                   if p.is_file() or p.is_symlink()})


def fingerprints(paths):
    return {str(real_path(p).relative_to(ROOT)): digest(p) for p in sorted(set(paths))}


def context_fingerprints(paths, lean_lib):
    result = {}
    for path in sorted(set(paths)):
        if path.is_relative_to(ROOT):
            key = "repository/" + str(real_path(path).relative_to(ROOT))
        else:
            require(path.is_relative_to(lean_lib) and path.is_file(),
                    f"Artifact outside the selected compiler: {path}")
            key = "toolchain/" + str(path.relative_to(lean_lib))
        result[key] = digest(path)
    return result


def audit_rows(text, api):
    counts = api.parse_audit_output(text, TARGETS)
    patterns = {
        "AUDIT_DECL": r"AUDIT_DECL: (\S+): (\S+)",
        "AUDIT_MODULE_COUNT": r"AUDIT_MODULE_COUNT: (\S+): (\d+)",
        "AUDIT_MODULE": r"AUDIT_MODULE: (\S+)",
        "AUDIT_COUNT": r"AUDIT_COUNT: (\d+)",
        "AUDIT_AXIOMS": r"AUDIT_AXIOMS: \[(.*)\]",
    }
    for line in text.splitlines():
        if "AUDIT_" in line:
            key = line.split(":", 1)[0]
            require(key in patterns and re.fullmatch(patterns[key], line) is not None,
                    f"Malformed or unexpected audit marker: {line}")
    rows = re.findall(r"^AUDIT_DECL: (\S+): (\S+)$", text, re.MULTILINE)
    require(len(rows) == len(set(rows)) == len({name for _, name in rows}),
            "Duplicate audit declarations")
    require(dict(Counter(owner for owner, _ in rows)) == counts,
            "Audit declaration rows disagree with module counts")
    for target in TARGETS:
        names = {name for owner, name in rows if owner == target}
        expected = {target + "." + name for name in EXPLICIT[target.rsplit(".", 1)[1]]}
        require(expected <= names, f"Missing explicit declarations: {sorted(expected - names)}")
    summaries = re.findall(r"^AUDIT_AXIOMS: \[(.*)\]$", text, re.MULTILINE)
    require(len(summaries) == 1, "Expected one native axiom summary")
    axioms = [name.strip() for name in summaries[0].split(",")] if summaries[0].strip() else []
    require(all(axioms) and len(axioms) == len(set(axioms)) and set(axioms) <= ALLOWED_AXIOMS,
            f"Invalid axiom summary: {axioms}")
    return {"module_counts": counts, "declaration_count": len(rows),
            "explicit_declaration_count": sum(map(len, EXPLICIT.values())),
            "axioms": axioms, "rows": rows}


def validate_search_path(text, lean_lib, *, built):
    paths = [Path(p).resolve() for p in text.strip().split(os.pathsep) if p]
    expected = {LIB, MATHLIB / ".lake/build/lib/lean",
                *(NATIVE / name / ".lake/build/lib/lean" for name in PINS)}
    require(len(paths) == len(set(paths)) and expected <= set(paths)
            and set(paths) <= expected | {lean_lib}, "Unexpected active LEAN_PATH")
    for path in paths:
        if path != lean_lib:
            # Lake lists registered libraries even if an unused one (e.g. Cli)
            # has never produced artifacts. Every actual import is checked below.
            real_path(path, exists=False)
    if not built:
        return paths
    for namespace, owner in (("InfoGeometry", LIB), ("DAG", LIB),
                             ("Mathlib", MATHLIB / ".lake/build/lib/lean")):
        first = next((p for p in paths if (p / namespace).is_dir()
                      or (p / (namespace + ".olean")).is_file()), None)
        require(first == owner, f"Namespace shadow in LEAN_PATH: {namespace}: {first}")
    return paths


def selected_evidence(module, lean, search_paths, build_text, before):
    relative = module.replace(".", "/")
    trace_path = LIB / (relative + ".trace")
    setup_path = IR / (relative + ".setup.json")
    trace = json.loads(real_path(trace_path).read_text())
    setup = json.loads(real_path(setup_path).read_text())
    require(trace.get("synthetic") is False and trace.get("schemaVersion") == "2025-09-10"
            and trace.get("inputs") and trace.get("outputs", {}).get("m") is False,
            f"Unsupported or synthetic selected trace: {module}")
    log = trace.get("log")
    require(isinstance(log, list) and log, f"Missing selected trace log: {module}")
    require(not any(e.get("level") in {"warning", "error"} for e in log),
            f"Selected module has a warning/error: {module}")
    labels = [entry[0] for entry in trace["inputs"]]
    for required in (COMPILER_TRACE, "Module.name: " + module,
                     "Package.id?: (some " + PACKAGE + ")", "Module.leanArgs: #[]"):
        require(labels.count(required) == 1, f"Missing exact trace identity: {module}: {required}")
    source = ROOT / "lean" / (relative + ".lean")
    require(sum(Path(label).resolve() == source for label in labels if label.endswith(".lean")) == 1,
            f"Selected trace does not name the current source: {module}")
    require(set(setup) == {"name", "package", "isModule", "options", "plugins", "dynlibs", "importArts"}
            and setup.get("name") == module and setup.get("package") == PACKAGE
            and setup.get("isModule") is False and setup.get("options") == {}
            and setup.get("plugins") == [] and setup.get("dynlibs") == [],
            f"Unexpected selected module setup: {module}")
    commands = [shlex.split(e["message"][3:]) for e in log
                if e.get("level") == "trace" and e.get("message", "").startswith(".> ")]
    require(len(commands) == 1 and len(commands[0]) == 12,
            f"Unexpected selected compiler invocation: {module}")
    argv = commands[0]
    # `lake env` appends the toolchain's Lake library directory; module builds
    # use Workspace.leanPath only (Lake.Config.Monad.getLeanPath).
    workspace_paths = [path for path in search_paths if path.is_relative_to(ROOT)]
    require(argv[0].startswith("LEAN_PATH=") and
            [Path(p).resolve() for p in argv[0][10:].split(os.pathsep)] == workspace_paths,
            f"Historical/foreign active compiler search path: {module}")
    require(Path(argv[1]).resolve() == lean and Path(argv[2]).resolve() == source
            and argv[3::2] == ["-o", "-i", "-c", "--setup", "--json"],
            f"Unexpected compiler executable or arguments: {module}")
    expected_outputs = [LIB / (relative + ".olean"), LIB / (relative + ".ilean"),
                        IR / (relative + ".c"), setup_path]
    require([Path(p).resolve() for p in argv[4:11:2]] == expected_outputs,
            f"Selected output path mismatch: {module}")
    artifacts, repo_modules = set(expected_outputs + [trace_path]), {module}
    for imported, groups in setup["importArts"].items():
        require(isinstance(groups, list) and groups and all(isinstance(g, list) for g in groups),
                f"Unsupported import artifact map: {imported}")
        flat = [Path(p).resolve() for group in groups for p in group]
        require(flat and all(any(p.is_relative_to(base) for base in search_paths) for p in flat),
                f"Import outside active source lane: {imported}")
        if imported.startswith(("InfoGeometry.", "DAG.")):
            expected = LIB / (imported.replace(".", "/") + ".olean")
            require(flat[0] == expected and all(p.is_relative_to(LIB) for p in flat),
                    f"Foreign repository import: {imported}")
            real_path(ROOT / "lean" / (imported.replace(".", "/") + ".lean"))
            repo_modules.add(imported)
        artifacts.update(flat)
    actions = re.findall(r"\b(Built|Replayed|Reused|Fetched|Unpacked) "
                         + re.escape(module) + r"(?=\s|$)", build_text)
    require(len(actions) <= 1, f"Ambiguous Lake job completion for {module}: {actions}")
    action = actions[0] if actions else "unchanged-selected-artifacts-no-build-reported"
    after = fingerprints(artifact_family(module))
    if not actions:
        proof_keys = [str(p.relative_to(ROOT)) for p in (trace_path, setup_path, expected_outputs[0])]
        require(all(key in before and before[key] == after.get(key) for key in proof_keys),
                f"Selected proof artifact changed without a recorded Lake action: {module}")
    return ({"lake_action": action, "fresh_compilation_this_run": action == "Built",
             "artifacts_present_before": bool(before), "warnings": 0,
             "source_sha256": digest(source), "artifact_sha256": after}, artifacts, repo_modules)


def verify_under_lock(lock, output: Path, *, require_fresh_targets: bool = False) -> dict:
    """The caller owns the already-acquired shared BuildLock for this entire call."""
    api = helpers()
    locks, build_api, runtime_api, bootstrap, audit_api, _ = api
    require(isinstance(lock, locks.BuildLock)
            and lock.lock_path.resolve() == locks.DEFAULT_BUILD_LOCK_PATH.resolve(),
            "An acquired maintained shared BuildLock is required")
    fd = lock.fileno()
    require((os.fstat(fd).st_dev, os.fstat(fd).st_ino)
            == (lock.lock_path.stat().st_dev, lock.lock_path.stat().st_ino),
            "BuildLock descriptor no longer names the shared lock")
    output = real_path(output, exists=False)
    require(output.is_relative_to(PROJECT / ".lake/verification") and not output.exists(),
            "Use a new output directory beneath this project's .lake/verification")
    output.mkdir(parents=True, exist_ok=False)
    report = {"schema": "info_geometry.dahm_scoped_lake.v1", "status": "failed",
              "scope": "Native scoped cached Lake build plus fresh selected-owner axiom audit; "
                       "not a fresh dependency build, cache reproducibility certification, or root publication gate",
              "targets": TARGETS, "require_fresh_targets": require_fresh_targets,
              "toolchain": TOOLCHAIN, "mathlib_pin": MATHLIB_REV,
              "started_utc": datetime.now(timezone.utc).isoformat(), "commands": [],
              "root_publication_gate": "not_run", "audit_freshly_elaborated": False}
    environment = os.environ.copy()
    for key in ("LEAN_PATH", "LEAN_SRC_PATH", "LEAN_SYSROOT", "LAKE_PKG_URL_MAP"):
        environment.pop(key, None)
    environment.update(ELAN_TOOLCHAIN=TOOLCHAIN, LAKE_ARTIFACT_CACHE="false",
                       LAKE_CONFIG=str(output / "absent-global-lake-config.toml"), NO_COLOR="1")
    baseline = None
    try:
        runtime_api.idle()
        print("[dahm-scoped] inspecting pinned sources and configuration", flush=True)
        before = identity_snapshot(api, sources=True)
        write_json(output / "sources-before.json", before)
        baseline = identity_snapshot(api)
        previous = {m: fingerprints(artifact_family(m)) for m in TARGETS}
        report["selected_artifacts_before"] = previous
        if require_fresh_targets:
            require(not any(previous.values()), "Fresh target mode requires absent selected artifact families; nothing was deleted")

        def run(label, arguments):
            require(identity_snapshot(api) == baseline, "Source-lane identity changed before " + label)
            require(not (output / "absent-global-lake-config.toml").exists(), "Unexpected global Lake configuration")
            runtime_api.idle()
            command = ["lake", "-d", str(PROJECT), *arguments]
            row = {"label": label, "argv": command, "cwd": str(ROOT), "exit_code": None}
            report["commands"].append(row)
            print(f"[dahm-scoped] starting {label}", flush=True)
            stdout_path, stderr_path = output / (label + ".stdout.log"), output / (label + ".stderr.log")
            process = None
            started = time.monotonic()
            try:
                with stdout_path.open("w") as stdout, stderr_path.open("w") as stderr:
                    process = subprocess.Popen(command, cwd=ROOT, env=environment,
                        stdin=subprocess.DEVNULL, stdout=stdout, stderr=stderr,
                        pass_fds=(fd,), start_new_session=True)
                    try:
                        row["exit_code"] = process.wait()
                    except KeyboardInterrupt:
                        build_api._interrupt_child_and_wait(process)
                        row["exit_code"] = process.returncode
                        raise
            finally:
                if process is not None and process.poll() is None:
                    build_api._interrupt_child_and_wait(process)
                row["seconds"] = round(time.monotonic() - started, 3)
                if stdout_path.exists():
                    row["stdout_sha256"] = digest(stdout_path)
                if stderr_path.exists():
                    row["stderr_sha256"] = digest(stderr_path)
                require(identity_snapshot(api) == baseline, "Source-lane identity changed after " + label)
                print(f"[dahm-scoped] finished {label}: exit={row['exit_code']} "
                      f"seconds={row['seconds']}", flush=True)
            require(row["exit_code"] == 0, f"Command failed: {label}; see {stderr_path}")
            return stdout_path.read_text(), stderr_path.read_text()

        banner, _ = run("lean-version", ["env", "lean", "--version"])
        report["lean_version"] = bootstrap.verify_version(TOOLCHAIN, banner)
        report["lake_version"] = run("lake-version", ["env", "lake", "--version"])[0].strip()
        lean_lib = Path(run("lean-libdir", ["env", "lean", "--print-libdir"])[0].strip()).resolve()
        lean = lean_lib.parents[1] / "bin/lean"
        lake = lean_lib.parents[1] / "bin/lake"
        require(lean.is_file() and lake.is_file(), "Missing selected compiler binaries")
        report["compiler_binaries"] = {str(p): digest(p) for p in (lean, lake)}
        search_text = run("lean-path-before", ["env", "printenv", "LEAN_PATH"])[0]
        search_paths = validate_search_path(search_text, lean_lib, built=False)
        report["lean_path"] = [str(p) for p in search_paths]
        stdout, stderr = run("build", ["--rehash", "--no-cache", "build", *TARGETS])
        validate_search_path(search_text, lean_lib, built=True)
        build_text = re.sub(r"\x1b\[[0-9;]*[A-Za-z]", "", stdout + "\n" + stderr)
        artifacts, repository_modules = set(), set()
        report["selected"] = {}
        for module in TARGETS:
            row, paths, owners = selected_evidence(module, lean, search_paths, build_text, previous[module])
            report["selected"][module] = row
            artifacts.update(paths)
            repository_modules.update(owners)
        if require_fresh_targets:
            require(all(row["fresh_compilation_this_run"] for row in report["selected"].values()),
                    "Fresh target mode requires a current Lake Built action for every selected owner")
        report["repository_import_owners"] = sorted(repository_modules)
        report["repository_source_sha256"] = {
            m: digest(ROOT / "lean" / (m.replace(".", "/") + ".lean")) for m in sorted(repository_modules)}
        audit = output / "ScopedOwnedDeclarations.lean"
        audit.write_text("/-\nCopyright (c) 2026 InfoGeometry Authors. All rights reserved.\n"
                         "Released under Apache 2.0 license as described in the file LICENSE.\n"
                         "Authors: InfoGeometry Engine Contributors\n-/\n\n"
                         + audit_api.audit_source(TARGETS))
        report["audit_source_sha256"] = digest(audit)
        report["audit_generator_sha256"] = digest(Path(audit_api.__file__))
        deps_text = run("audit-deps", ["env", "lean", "--deps", str(audit)])[0]
        dependencies = {Path(line.strip()).resolve() for line in deps_text.splitlines() if line.strip().endswith(".olean")}
        require({LIB / (m.replace(".", "/") + ".olean") for m in TARGETS} <= dependencies,
                "Fresh audit did not resolve all selected modules to the scoped outputs")
        require(all(any(p.is_relative_to(base) for base in [*search_paths, lean_lib]) for p in dependencies),
                "Fresh audit resolved imports outside the selected runtime")
        artifacts.update(dependencies)
        # Hash the actual selected setup import families, including private/IR artifacts.
        artifact_before = context_fingerprints(artifacts, lean_lib)
        write_json(output / "import-artifacts-before.json", artifact_before)
        stdout, stderr = run("audit", ["env", "lean", str(audit)])
        require(not re.search(r"\b(?:warning|error):", stdout + "\n" + stderr), "Fresh audit emitted a diagnostic")
        report["audit"] = audit_rows(stdout, audit_api)
        report["audit_freshly_elaborated"] = True
        require(digest(audit) == report["audit_source_sha256"], "Generated audit source changed")
        require(run("lean-path-after", ["env", "printenv", "LEAN_PATH"])[0] == search_text,
                "Audit search path changed")
        artifact_after = context_fingerprints(artifacts, lean_lib)
        write_json(output / "import-artifacts-after.json", artifact_after)
        require(artifact_after == artifact_before, "Imported artifact bytes changed during the audit")
        require(report["compiler_binaries"] == {str(p): digest(p) for p in (lean, lake)},
                "Compiler binaries changed during verification")
        after = identity_snapshot(api, sources=True)
        write_json(output / "sources-after.json", after)
        require(after == before, "Source/config/dependency bytes changed during verification")
        report["status"] = "passed"
    except BaseException as error:
        report["error"] = repr(error)
        (output / "failure.log").write_text(traceback.format_exc())
        raise
    finally:
        report["finished_utc"] = datetime.now(timezone.utc).isoformat()
        write_json(output / "scoped-receipt.json", report)
        write_json(output / "evidence-sha256.json", {
            p.name: digest(p) for p in sorted(output.iterdir())
            if p.is_file() and p.name != "evidence-sha256.json"})
    return report


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--output", type=Path,
                        help="New directory beneath verification/dahm-exterior-square/.lake/verification")
    parser.add_argument("--require-fresh-targets", action="store_true")
    parser.add_argument("--wait-for-build-lock", action="store_true")
    args = parser.parse_args()
    locks = helpers()[0]
    output = args.output or PROJECT / ".lake/verification" / (
        datetime.now(timezone.utc).strftime("%Y%m%dT%H%M%SZ-") + uuid.uuid4().hex[:8])
    with locks.BuildLock(locks.DEFAULT_BUILD_LOCK_PATH, "dahm-exterior-square-scoped",
                         block=args.wait_for_build_lock) as lock:
        report = verify_under_lock(lock, output, require_fresh_targets=args.require_fresh_targets)
    print(json.dumps({"status": report["status"], "receipt": str(output / "scoped-receipt.json")}, indent=2))


if __name__ == "__main__":
    try:
        main()
    except KeyboardInterrupt:
        raise SystemExit(130)
