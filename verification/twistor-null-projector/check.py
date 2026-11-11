#!/usr/bin/env python3
"""Fresh repository-closure compilation and selected-owner axiom audit.

This freezes the fourteen canonical repository owners into a new regular Lake
package. Its two selected owners receive a fresh complete declaration audit.
Native dependency artifacts may be reused at the exact reviewed pins. This is
not a fresh Mathlib build, cache provenance or hermeticity certification, an
audit of every imported declaration, or the root project's publication gate.
No repository oleans are seeded into the fresh package, and the checker does
not manually edit or delete artifacts. Lake may reuse or build native dependencies.
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
import shutil
import subprocess
import sys
import time
import tomllib
import traceback
import uuid

SCOPE = Path(__file__).resolve().parent
ROOT = SCOPE.parents[1]
TOOLCHAIN = "leanprover/lean4:v4.34.1"
COMPILER_COMMIT = "5045d0056413266e57c625dcd7c365b10e377c52"
COMPILER_TRACE = "Lean 4.34.1, commit " + COMPILER_COMMIT
MATHLIB_REV = "d13f23b723b8a846827a245b89c10fc7d3f11612"
PACKAGE = "twistor_null_projector_validation"
MATHLIB = ROOT / ".lake/packages/mathlib"
NATIVE = MATHLIB / ".lake/packages"
OUTPUT_ROOT = ROOT / ".git/twistor-null-projector/checks"
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
    "InfoGeometry.LinearAlgebra.IsotropicSelfAdjoint": """
        square_zero_iff_image_isotropic
        eq_zero_of_idempotent_of_image_isotropic""".split(),
    "InfoGeometry.Twistor.PenroseNullProjector": """
        twistorHermitian_flip_separatingLeft incidenceEmbedding
        incidenceEmbedding_apply incidenceEmbedding_injective
        incidenceEmbedding_isotropic eq_zero_of_selfAdjoint_of_range_le_incidence
        incidenceProjection incidenceProjection_apply incidenceProjection_on_incidence
        incidenceProjection_idempotent incidenceProjection_range
        incidenceProjection_finrank_range incidenceProjection_ne_zero
        incidenceProjection_not_selfAdjoint""".split(),
}
TARGETS = list(EXPLICIT)
EXPECTED_OWNERS = set("""
    InfoGeometry.Algebra.FiniteSpinAlgebra
    InfoGeometry.Cartan.Involution
    InfoGeometry.Convex.ProjectiveRays
    InfoGeometry.GrandUnification.ArchetypeDictionary
    InfoGeometry.Krein.DoubledSpace
    InfoGeometry.Krein.InvolutiveSelfDualCarrier
    InfoGeometry.Krein.KreinSpace
    InfoGeometry.LinearAlgebra.IsotropicSelfAdjoint
    InfoGeometry.Physics.ChiralPoincareSouriauBridge
    InfoGeometry.Twistor.NullProjective
    InfoGeometry.Twistor.PenroseIncidence
    InfoGeometry.Twistor.PenroseTwistor
    InfoGeometry.Twistor.PerjesConventions
    InfoGeometry.Twistor.PenroseNullProjector
""".split())
ALLOWED_AXIOMS = {"propext", "Classical.choice", "Quot.sound"}
HEADER = ("/-\nCopyright (c) 2026 InfoGeometry Authors. All rights reserved.\n"
          "Released under Apache 2.0 license as described in the file LICENSE.\n"
          "Authors: InfoGeometry Engine Contributors\n-/\n\n")


def require(condition, message):
    if not condition:
        raise RuntimeError(message)


def sha(path):
    result = hashlib.sha256()
    with Path(path).open("rb") as stream:
        for block in iter(lambda: stream.read(1024 * 1024), b""):
            result.update(block)
    return result.hexdigest()


def object_sha(value):
    return hashlib.sha256(json.dumps(value, sort_keys=True).encode()).hexdigest()


def write_json(path, value):
    Path(path).write_text(json.dumps(value, indent=2, sort_keys=True) + "\n")


def canonical(path, *, base=ROOT, exists=True):
    path = Path(os.path.abspath(path))
    require(base is None or path.is_relative_to(base), f"Path outside approved root: {path}")
    require(all(not p.is_symlink() for p in (path, *path.parents)),
            f"Symlink in active verification path: {path}")
    require(path.resolve() == path, f"Noncanonical verification path: {path}")
    if exists:
        require(path.exists(), f"Missing verification input: {path}")
    return path


def git(directory, *arguments):
    return subprocess.check_output(["git", "--no-optional-locks", *arguments],
                                   cwd=directory, text=True)


def helpers():
    require(SCOPE == ROOT / "verification/twistor-null-projector",
            "Run the integrated verification/twistor-null-projector/check.py")
    sys.path.insert(0, str(ROOT))
    from tools import build_lock
    from tools.infra import build, check_runtime_acceptance, ci_bootstrap
    from tools.quality import reviewed_audit_source, reviewed_native
    result = (build_lock, build, check_runtime_acceptance, ci_bootstrap,
              reviewed_audit_source, reviewed_native)
    for module in result:
        require(canonical(module.__file__).is_relative_to(ROOT / "tools"),
                f"Foreign verification helper: {module.__file__}")
    return result


def imports(path):
    """Read the reviewed ordinary header grammar, rejecting unsupported headers.

    Native --deps and setup evidence later independently check actual imports.
    Nested leading comments are handled; module/prelude/quoted or multiline
    imports require source review instead of silently extending the closure.
    """
    text, position, result = path.read_text(), 0, []
    while position < len(text):
        if text[position].isspace():
            position += 1
            continue
        if text.startswith("--", position):
            position = text.find("\n", position)
            if position < 0:
                break
            continue
        if text.startswith("/-", position):
            depth, position = 1, position + 2
            while depth and position < len(text):
                if text.startswith("/-", position):
                    depth, position = depth + 1, position + 2
                elif text.startswith("-/", position):
                    depth, position = depth - 1, position + 2
                else:
                    position += 1
            require(depth == 0, f"Unclosed header comment: {path}")
            continue
        match = re.match(r"import[ \t]+([^\n\r]+)", text[position:])
        if match is None:
            require(re.match(r"(?:module|prelude|public|private|import)\b", text[position:]) is None,
                    f"Unreviewed import header grammar: {path}")
            break
        names = match[1].split("--", 1)[0].split()
        require(names and all(re.fullmatch(r"[A-Za-z_][A-Za-z0-9_']*(?:\.[A-Za-z_][A-Za-z0-9_']*)*", n)
                              for n in names), f"Unsupported import names: {path}")
        result.extend(names)
        position += match.end()
    require(result, f"No ordinary imports found: {path}")
    return result


def closure():
    result, active = {}, set()

    def visit(module):
        require(module not in active, f"Repository import cycle: {module}")
        if module in result:
            return
        active.add(module)
        source = canonical(ROOT / "lean" / (module.replace(".", "/") + ".lean"))
        dependencies = imports(source)
        for dependency in dependencies:
            if dependency.startswith("InfoGeometry."):
                visit(dependency)
            else:
                require(dependency.split(".")[0] in {"Mathlib", "Init", "Lean", "Std"},
                        f"Unreviewed import namespace: {module}: {dependency}")
        active.remove(module)
        result[module] = {"source": str(source), "sha256": sha(source), "imports": dependencies}

    for module in TARGETS:
        visit(module)
    require(set(result) == EXPECTED_OWNERS, "Repository import closure needs source re-review")
    return result


def identity_snapshot(api):
    """Full source inventories include ignored sources, on every invocation."""
    _, build, _, _, _, native = api
    for directory in (ROOT, SCOPE, MATHLIB, NATIVE):
        canonical(directory)
        error = build._validate_lake_workspace_integrity(directory)
        require(error is None, error)
    require((ROOT / ".git").is_dir(), "An independent regular checkout is required")
    root_manifest = json.loads((ROOT / "lake-manifest.json").read_text())
    root_mathlib = [p for p in root_manifest["packages"] if p["name"] == "mathlib"]
    require(len(root_mathlib) == 1 and root_mathlib[0]["type"] == "git"
            and root_mathlib[0]["rev"] == MATHLIB_REV, "Root Mathlib pin differs")
    for directory in (ROOT, SCOPE, MATHLIB):
        require((directory / "lean-toolchain").read_text() == TOOLCHAIN + "\n",
                f"Toolchain mismatch: {directory}")
    config = tomllib.loads((SCOPE / "lakefile.toml").read_text())
    require(config == {
        "name": PACKAGE, "srcDir": "../../lean",
        "packagesDir": "../../.lake/packages/mathlib/.lake/packages",
        "enableArtifactCache": False, "defaultTargets": TARGETS,
        "require": [{"name": "mathlib", "path": "../../.lake/packages/mathlib"}],
        "lean_lib": [{"name": "InfoGeometry"}],
    }, "Scoped configuration needs source re-review")
    require(not (SCOPE / "lakefile.lean").exists(), "Ambiguous scoped Lake configuration")
    manifest = json.loads((SCOPE / "lake-manifest.json").read_text())
    require(manifest.get("version") == "1.2.0" and manifest.get("name") == PACKAGE
            and manifest.get("lakeDir") == ".lake" and manifest.get("fixedToolchain") is True
            and manifest.get("packagesDir") == config["packagesDir"], "Scoped manifest metadata differs")
    entries = {p["name"]: p for p in manifest["packages"]}
    require(len(entries) == len(manifest["packages"]) == 9
            and set(entries) == {"mathlib", *PINS}, "Unexpected scoped dependencies")
    require(entries["mathlib"] == {
        "name": "mathlib", "type": "path", "dir": "../../.lake/packages/mathlib",
        "scope": "", "inherited": False, "configFile": "lakefile.lean",
        "manifestFile": "lake-manifest.json",
    }, "Unexpected Mathlib path dependency")
    native_manifest = json.loads((MATHLIB / "lake-manifest.json").read_text())
    inherited = {p["name"]: p for p in native_manifest["packages"]}
    require(len(inherited) == len(native_manifest["packages"]) == 8
            and set(inherited) == set(PINS) and native_manifest["packagesDir"] == ".lake/packages",
            "Unexpected native dependency graph")
    for name, revision in PINS.items():
        require(inherited[name]["type"] == "git" and inherited[name]["rev"] == revision
                and entries[name] == {**inherited[name], "inherited": True},
                f"Native inherited pin differs: {name}")
    packages = {}
    for name, revision, directory in [("mathlib", MATHLIB_REV, MATHLIB),
            *((n, rev, NATIVE / n) for n, rev in PINS.items())]:
        canonical(directory)
        error = build._validate_lake_workspace_integrity(directory)
        require(error is None, error)
        identity = native.checkout_status(directory, revision)
        require(identity.get("clean") is True, f"Unclean or mismatched native checkout: {name}: {identity}")
        inventory = native.source_files(directory)
        tracked = set(git(directory, "ls-files", "-z").split("\0"))
        for relative, row in inventory.items():
            if relative.endswith(".lean"):
                require(relative in tracked, f"Untracked/ignored native Lean source: {directory / relative}")
            if row["link"] is not None:
                require(relative in tracked and Path(row["resolved"]).is_relative_to(ROOT),
                        f"Unreviewed native source alias: {directory / relative}")
        packages[name] = {"path": str(directory), "identity": identity, "sources": inventory}
    for directory in (ROOT, SCOPE, *(Path(p["path"]) for p in packages.values())):
        require(not (directory / ".lake/package-overrides.json").exists(),
                f"Unreviewed package overrides: {directory}")
    watched = [ROOT / name for name in (
        "lean-toolchain", "lakefile.lean", "lake-manifest.json", ".gitmodules",
        "docs/TWISTOR_NULL_PROJECTOR_CONTRACT.md", "docs/TWISTOR_NULL_PROJECTOR_INTAKE_BG.md",
        "tools/quality/check_perjes_klein_targets.txt")]
    watched += [SCOPE / name for name in ("check.py", "lakefile.toml", "lake-manifest.json", "lean-toolchain")]
    tools = native.source_files(ROOT / "tools")
    tracked = set(git(ROOT, "ls-files", "-z").split("\0"))
    for relative, row in tools.items():
        if row["link"] is not None:
            require("tools/" + relative in tracked and Path(row["resolved"]).is_relative_to(ROOT),
                    f"Unreviewed tool alias: {relative}")
    index = git(ROOT, "ls-files", "--stage", "-z")
    owners = closure()
    return {"root_head": git(ROOT, "rev-parse", "HEAD").strip(),
            "root_status": git(ROOT, "status", "--porcelain", "--untracked-files=all"),
            "root_index_sha256": hashlib.sha256(index.encode()).hexdigest(),
            "selected_index_entries": [entry for entry in index.split("\0")
                if entry and entry.split("\t", 1)[1] in {
                    str(Path(row["source"]).relative_to(ROOT)) for row in owners.values()}],
            "watched_inputs": {str(p.relative_to(ROOT)): sha(canonical(p)) for p in watched},
            "repository_import_closure": owners, "tools_sources": tools, "native_packages": packages}


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
                    f"Malformed/unexpected native audit marker: {line}")
    rows = re.findall(r"^AUDIT_DECL: (\S+): (\S+)$", text, re.MULTILINE)
    require(len(rows) == len(set(rows)) == len({name for _, name in rows}), "Duplicate audit declarations")
    require(dict(Counter(owner for owner, _ in rows)) == counts, "Audit declaration/count disagreement")
    for owner, suffixes in EXPLICIT.items():
        expected = {owner + "." + suffix for suffix in suffixes}
        actual = {name for module, name in rows if module == owner}
        require(expected <= actual, f"Missing explicit declarations: {sorted(expected - actual)}")
    summaries = re.findall(r"^AUDIT_AXIOMS: \[(.*)\]$", text, re.MULTILINE)
    require(len(summaries) == 1, "Expected one native axiom summary")
    axioms = [a.strip() for a in summaries[0].split(",")] if summaries[0].strip() else []
    require(all(axioms) and len(axioms) == len(set(axioms)) and set(axioms) <= ALLOWED_AXIOMS,
            f"Invalid native axiom summary: {axioms}")
    return {"module_counts": counts, "declaration_count": len(rows), "rows": rows,
            "explicit_declaration_count": sum(map(len, EXPLICIT.values())), "axioms": axioms}


def artifact_family(package, module):
    relative = Path(module.replace(".", "/"))
    return {p for directory in (package / ".lake/build/lib/lean", package / ".lake/build/ir")
            for p in (directory / relative.parent).glob(relative.name + ".*")
            if p.is_file() or p.is_symlink()}


def fingerprints(paths, lean_lib=None):
    result = {}
    for path in sorted(set(paths)):
        base = ROOT if path.is_relative_to(ROOT) else lean_lib
        require(base is not None, f"Artifact outside approved roots: {path}")
        path = canonical(path, base=base)
        require(path.is_file(), f"Not a regular verification artifact: {path}")
        result[str(path)] = sha(path)
    return result


def search_paths(text, package, lean_lib, *, built):
    fields = text.strip().split(os.pathsep)
    require(all(fields), "Empty entry in LEAN_PATH")
    paths = [canonical(p, base=None, exists=False) for p in fields]
    lib = package / ".lake/build/lib/lean"
    expected = {lib, MATHLIB / ".lake/build/lib/lean",
                *(NATIVE / name / ".lake/build/lib/lean" for name in PINS)}
    require(len(paths) == len(set(paths)) and expected <= set(paths)
            and set(paths) <= expected | {lean_lib}, "Unexpected active LEAN_PATH")
    if built:
        for namespace, owner in (("InfoGeometry", lib), ("Mathlib", MATHLIB / ".lake/build/lib/lean")):
            first = next((p for p in paths if (p / namespace).is_dir()
                          or (p / (namespace + ".olean")).is_file()), None)
            require(first == owner, f"Namespace shadow in LEAN_PATH: {namespace}: {first}")
    return paths


def resolve_import(module, paths, lean_lib):
    # Lean selects the first root containing the top-level namespace, not the
    # first root containing the full module file (Lean.Util.Path.findWithExt).
    namespace = module.split(".")[0]
    roots = paths if lean_lib in paths else [*paths, lean_lib]
    owner = next((p for p in roots if (p / namespace).is_dir()
                  or (p / (namespace + ".olean")).is_file()), None)
    require(owner is not None, f"Unresolved native namespace: {module}")
    return canonical(owner / (module.replace(".", "/") + ".olean"), base=owner)


def compilation_evidence(module, package, lean, paths, build_text):
    lib, ir = package / ".lake/build/lib/lean", package / ".lake/build/ir"
    relative = module.replace(".", "/")
    source = package / "lean" / (relative + ".lean")
    trace_path, setup_path = lib / (relative + ".trace"), ir / (relative + ".setup.json")
    trace = json.loads(canonical(trace_path).read_text())
    setup = json.loads(canonical(setup_path).read_text())
    require(trace.get("synthetic") is False and trace.get("schemaVersion") == "2025-09-10"
            and trace.get("inputs") and trace.get("outputs", {}).get("m") is False,
            f"Unsupported/synthetic repository trace: {module}")
    log = trace.get("log")
    require(isinstance(log, list) and log, f"Missing compiler trace log: {module}")
    warnings = [e for e in log if e.get("level") == "warning"]
    require(not any(e.get("level") == "error" for e in log), f"Repository compiler error: {module}")
    require(module not in TARGETS or not warnings, f"Selected owner emitted warnings: {module}")
    labels = [entry[0] for entry in trace["inputs"]]
    for required in (COMPILER_TRACE, "Module.name: " + module,
                     "Package.id?: (some " + PACKAGE + ")", "Module.leanArgs: #[]"):
        require(labels.count(required) == 1, f"Missing exact trace identity: {module}: {required}")
    require(sum(Path(label) == source for label in labels if label.endswith(".lean")) == 1,
            f"Trace does not name the fresh copied source: {module}")
    require(set(setup) == {"name", "package", "isModule", "options", "plugins", "dynlibs", "importArts"}
            and setup["name"] == module and setup["package"] == PACKAGE
            and setup["isModule"] is False and setup["options"] == {}
            and setup["plugins"] == [] and setup["dynlibs"] == [], f"Unexpected setup: {module}")
    commands = [shlex.split(e["message"][3:]) for e in log
                if e.get("level") == "trace" and e.get("message", "").startswith(".> ")]
    require(len(commands) == 1 and len(commands[0]) == 12, f"Unexpected compiler invocation: {module}")
    argv = commands[0]
    workspace_paths = [p for p in paths if p.is_relative_to(ROOT)]
    require(argv[0].startswith("LEAN_PATH=") and
            [Path(p) for p in argv[0][10:].split(os.pathsep)] == workspace_paths,
            f"Foreign active compiler search path: {module}")
    require(Path(argv[1]) == lean and Path(argv[2]) == source
            and argv[3::2] == ["-o", "-i", "-c", "--setup", "--json"],
            f"Unexpected compiler executable/arguments: {module}")
    outputs = [lib / (relative + ".olean"), lib / (relative + ".ilean"), ir / (relative + ".c"), setup_path]
    require([Path(p) for p in argv[4:11:2]] == outputs, f"Foreign repository output path: {module}")
    artifacts = set(outputs + [trace_path]) | artifact_family(package, module)
    for imported, groups in setup["importArts"].items():
        require(isinstance(groups, list) and groups and all(isinstance(g, list) for g in groups),
                f"Unsupported import artifact map: {module}: {imported}")
        flat = [Path(p) for group in groups for p in group]
        require(flat and all(p.is_absolute() and any(p.is_relative_to(base) for base in paths) for p in flat),
                f"Import outside active artifact roots: {module}: {imported}")
        if imported.startswith("InfoGeometry."):
            require(imported in EXPECTED_OWNERS
                    and lib / (imported.replace(".", "/") + ".olean") in flat
                    and all(p.is_relative_to(lib) for p in flat), f"Foreign repository artifact: {imported}")
        artifacts.update(flat)
    actions = re.findall(r"\b(Built|Replayed|Reused|Fetched|Unpacked) "
                         + re.escape(module) + r"(?=\s|$)", build_text)
    require(actions == ["Built"], f"No unique fresh Lake Built action for {module}: {actions}")
    return {"lake_action": "Built", "fresh_compilation_this_run": True,
            "source_sha256": sha(source), "warning_count": len(warnings),
            "warnings": warnings, "artifact_sha256": fingerprints(artifact_family(package, module))}, artifacts


def verify_under_lock(lock, output: Path, *, lake_command="lake"):
    api = helpers()
    locks, build, runtime, bootstrap, audit_api, native = api
    require(isinstance(lock, locks.BuildLock), "A maintained BuildLock is required")
    fd = lock.fileno()
    held, shared = os.fstat(fd), os.stat(locks.DEFAULT_BUILD_LOCK_PATH)
    require((held.st_dev, held.st_ino) == (shared.st_dev, shared.st_ino), "Wrong shared build-lock descriptor")
    output = canonical(output, exists=False)
    require(output.is_relative_to(OUTPUT_ROOT) and not output.exists(),
            "Use a new directory beneath .git/twistor-null-projector/checks; evidence is never deleted")
    output.mkdir(parents=True, exist_ok=False)
    report = {"schema": "info_geometry.twistor_null_projector.scoped.v1", "status": "failed",
              "started_utc": datetime.now(timezone.utc).isoformat(), "commands": [],
              "scope": "Fresh 14-owner repository closure; fresh complete audit of the two selected owners; "
                       "native caches reused; no hermeticity, native-cache provenance, or root-gate claim",
              "targets": TARGETS, "toolchain": TOOLCHAIN, "mathlib_pin": MATHLIB_REV,
              "root_publication_gate": "not_run", "audit_freshly_elaborated": False}
    before = frozen_before = None
    package = output / "package"
    try:
        print("[twistor-null-projector] inspecting pinned inputs after lock acquisition", flush=True)
        runtime.idle()
        before = identity_snapshot(api)
        write_json(output / "sources-before.json", before)
        package.mkdir()
        for module, row in before["repository_import_closure"].items():
            destination = package / "lean" / (module.replace(".", "/") + ".lean")
            destination.parent.mkdir(parents=True, exist_ok=True)
            shutil.copyfile(row["source"], destination)
            require(sha(destination) == row["sha256"], f"Source changed while freezing: {module}")
        config = (f'name = "{PACKAGE}"\nsrcDir = "lean"\npackagesDir = {json.dumps(str(NATIVE))}\n'
                  f'enableArtifactCache = false\ndefaultTargets = {json.dumps(TARGETS)}\n\n'
                  f'[[require]]\nname = "mathlib"\npath = {json.dumps(str(MATHLIB))}\n\n'
                  '[[lean_lib]]\nname = "InfoGeometry"\n')
        (package / "lakefile.toml").write_text(config)
        (package / "lean-toolchain").write_text(TOOLCHAIN + "\n")
        manifest = json.loads((SCOPE / "lake-manifest.json").read_text())
        manifest["packagesDir"] = str(NATIVE)
        next(p for p in manifest["packages"] if p["name"] == "mathlib")["dir"] = str(MATHLIB)
        write_json(package / "lake-manifest.json", manifest)
        audit = package / "AxiomAudit.lean"
        audit.write_text(HEADER + audit_api.audit_source(TARGETS))
        frozen_before = native.source_files(package)
        require(all(row["link"] is None for row in frozen_before.values()), "Aliased frozen input")
        write_json(output / "frozen-inputs-before.json", frozen_before)
        report["repository_import_closure"] = list(before["repository_import_closure"])
        report["audit_source_sha256"] = sha(audit)
        report["audit_generator_sha256"] = sha(Path(audit_api.__file__))
        report["repository_artifacts_absent_before"] = {
            module: not artifact_family(package, module) for module in EXPECTED_OWNERS}
        require(not (package / ".lake").exists() and all(report["repository_artifacts_absent_before"].values()),
                "Fresh package already contains build artifacts")
        environment = os.environ.copy()
        removed = [key for key in environment if key.startswith(("LEAN_", "LAKE_"))
                   or key in {"LEAN", "LAKE", "LD_PRELOAD", "LD_LIBRARY_PATH", "DYLD_LIBRARY_PATH", "DYLD_INSERT_LIBRARIES"}]
        for key in removed:
            environment.pop(key, None)
        environment.update(ELAN_TOOLCHAIN=TOOLCHAIN, LAKE_NO_CACHE="true", LAKE_ARTIFACT_CACHE="false",
                           LAKE_RESTORE_ARTIFACTS="false", LAKE_CACHE_DIR="",
                           LAKE_CONFIG=str(output / "absent-global-lake-config.toml"), NO_COLOR="1")
        launcher = shutil.which(lake_command)
        require(launcher is not None, f"Lake executable not found: {lake_command}")
        lake = canonical(Path(launcher).resolve(), base=None)
        python = canonical(Path(sys.executable).resolve(), base=None)
        environment["PATH"] = str(lake.parent) + os.pathsep + environment.get("PATH", "")
        executables = {str(p): sha(p) for p in (lake, python)}
        artifact_paths, artifact_before, lean_lib = set(), None, None
        report["removed_environment_keys"] = sorted(removed)
        report["controlled_environment"] = {key: environment[key] for key in (
            "ELAN_TOOLCHAIN", "LAKE_NO_CACHE", "LAKE_ARTIFACT_CACHE", "LAKE_RESTORE_ARTIFACTS", "LAKE_CACHE_DIR", "LAKE_CONFIG")}

        def stable(label):
            current = identity_snapshot(api)
            if current != before:
                write_json(output / (label + ".source-drift.json"), current)
                raise RuntimeError("Source/config/native identity changed: " + label)
            require(native.source_files(package) == frozen_before, "Frozen package input changed: " + label)
            require(not (package / ".lake/package-overrides.json").exists()
                    and not (output / "absent-global-lake-config.toml").exists(), "Unexpected configuration override")
            require(executables == {path: sha(canonical(path, base=None)) for path in executables},
                    "Verification executable changed: " + label)
            if artifact_before is not None:
                require(fingerprints(artifact_paths, lean_lib) == artifact_before,
                        "Consumed artifact bytes changed: " + label)
            return object_sha(current)

        def run(label, arguments):
            row = {"label": label, "argv": [str(lake), "-d", str(package), *arguments],
                   "cwd": str(ROOT), "exit_code": None}
            report["commands"].append(row)
            print(f"[twistor-null-projector] starting {label}", flush=True)
            row["before_source_snapshot_sha256"] = stable(label + "-before")
            runtime.idle()
            stdout_path, stderr_path = output / (label + ".stdout.log"), output / (label + ".stderr.log")
            process, started = None, time.monotonic()
            try:
                with stdout_path.open("w") as stdout, stderr_path.open("w") as stderr:
                    process = subprocess.Popen(row["argv"], cwd=ROOT, env=environment,
                        stdin=subprocess.DEVNULL, stdout=stdout, stderr=stderr,
                        pass_fds=(fd,), start_new_session=True)
                    try:
                        row["exit_code"] = process.wait()
                    except KeyboardInterrupt:
                        build._interrupt_child_and_wait(process)
                        row["exit_code"] = process.returncode
                        raise
            finally:
                if process is not None and process.poll() is None:
                    build._interrupt_child_and_wait(process)
                row["seconds"] = round(time.monotonic() - started, 3)
                for kind, path in (("stdout", stdout_path), ("stderr", stderr_path)):
                    if path.exists():
                        row[kind + "_file"] = path.name
                        row[kind + "_sha256"] = sha(path)
                unwinding = sys.exc_info()[0] is not None
                try:
                    row["after_source_snapshot_sha256"] = stable(label + "-after")
                except BaseException as error:
                    row["after_integrity_error"] = repr(error)
                    if not unwinding:
                        raise
                print(f"[twistor-null-projector] finished {label}: exit={row['exit_code']} seconds={row['seconds']}", flush=True)
            require(row["exit_code"] == 0, f"Native step failed: {label}; see {stdout_path} and {stderr_path}")
            return stdout_path.read_text(), stderr_path.read_text()

        def quiet(stdout, stderr):
            require(not re.search(r"\b(?:warning|error):", stdout + "\n" + stderr),
                    "Selected file/audit/environment/dependency check emitted a diagnostic")

        banner, stderr = run("lean-version", ["env", "lean", "--version"])
        quiet(banner, stderr)
        report["lean_version"] = bootstrap.verify_version(TOOLCHAIN, banner)
        require(re.search(r"\bcommit " + COMPILER_COMMIT + r"(?=[,)\s])", banner), "Unexpected compiler commit")
        report["lean_version_banner"] = banner.strip()
        report["lake_version"] = run("lake-version", ["env", "lake", "--version"])[0].strip()
        lib_text, stderr = run("lean-libdir", ["env", "lean", "--print-libdir"])
        quiet(lib_text, stderr)
        lean_lib = canonical(lib_text.strip(), base=None)
        sysroot = lean_lib.parents[1]
        require(lean_lib == sysroot / "lib/lean", "Unexpected compiler installation layout")
        lean, selected_lake = (canonical(sysroot / "bin" / name, base=None) for name in ("lean", "lake"))
        executables.update({str(p): sha(p) for p in (lean, selected_lake)})
        probe = ("import json,os,shutil; "
                 "keys=['LEAN_PATH','LEAN_SRC_PATH','LEAN_SYSROOT','LEAN_GITHASH','ELAN_TOOLCHAIN',"
                 "'LAKE_CONFIG','LAKE_PKG_URL_MAP','LAKE_NO_CACHE','LAKE_ARTIFACT_CACHE','LAKE_RESTORE_ARTIFACTS']; "
                 "print(json.dumps({'environment':{k:os.environ.get(k) for k in keys},"
                 "'lean':shutil.which('lean'),'lake':shutil.which('lake')},sort_keys=True))")
        runtime_text, stderr = run("runtime-before", ["env", str(python), "-c", probe])
        quiet(runtime_text, stderr)
        metadata = json.loads(runtime_text)
        active = metadata["environment"]
        require(metadata["lean"] == str(lean) and metadata["lake"] == str(selected_lake)
                and active["LEAN_SYSROOT"] == str(sysroot) and active["LEAN_GITHASH"] == COMPILER_COMMIT
                and active["ELAN_TOOLCHAIN"] == TOOLCHAIN, "Unexpected active compiler selection")
        require(json.loads(active["LAKE_PKG_URL_MAP"]) == {}
                and active["LAKE_CONFIG"] == environment["LAKE_CONFIG"]
                and active["LAKE_NO_CACHE"] == "true" and active["LAKE_ARTIFACT_CACHE"] == "false"
                and active["LAKE_RESTORE_ARTIFACTS"] == "false", "Unexpected active Lake override")
        paths = search_paths(active["LEAN_PATH"], package, lean_lib, built=False)
        for entry in active["LEAN_SRC_PATH"].split(os.pathsep):
            source_path = canonical(entry, base=None, exists=False)
            require(any(source_path.is_relative_to(base) for base in (package / "lean", MATHLIB, sysroot / "src")),
                    f"Foreign source search path: {source_path}")
        report["runtime"] = metadata
        report["executables_sha256"] = executables
        lake = selected_lake
        stdout, stderr = run("fresh-build", ["--rehash", "--no-cache", "build", *TARGETS])
        search_paths(active["LEAN_PATH"], package, lean_lib, built=True)
        build_text = re.sub(r"\x1b\[[0-9;]*[A-Za-z]", "", stdout + "\n" + stderr)
        report["compiled_owners"] = {}
        for module in before["repository_import_closure"]:
            evidence, consumed = compilation_evidence(module, package, lean, paths, build_text)
            report["compiled_owners"][module] = evidence
            artifact_paths.update(consumed)
        audit_imports = [*TARGETS, "Lean.Util.CollectAxioms", "Lean.Elab.Command"]
        for row in before["repository_import_closure"].values():
            artifact_paths.update(resolve_import(m, paths, lean_lib) for m in ["Init", *row["imports"]])
        artifact_paths.update(resolve_import(m, paths, lean_lib) for m in ["Init", *audit_imports])
        artifact_before = fingerprints(artifact_paths, lean_lib)
        write_json(output / "artifacts-before.json", artifact_before)
        report["dependency_resolution"] = {}
        checks = [(m, package / "lean" / (m.replace(".", "/") + ".lean"), row["imports"])
                  for m, row in before["repository_import_closure"].items()]
        checks.append(("AxiomAudit", audit, audit_imports))
        for module, source, declared in checks:
            stdout, stderr = run("deps-" + module, ["env", "lean", "--deps", str(source)])
            quiet(stdout, stderr)
            lines = [line.strip() for line in stdout.splitlines() if line.strip()]
            require(lines and all(line.endswith(".olean") and Path(line).is_absolute() for line in lines),
                    f"Unexpected --deps output: {module}")
            actual = {Path(line) for line in lines}
            expected = {resolve_import(m, paths, lean_lib) for m in ["Init", *declared]}
            require(actual == expected, f"Native dependency resolution differs from frozen imports: {module}")
            require(actual <= artifact_paths, f"Dependency artifact missing from byte stability evidence: {module}")
            report["dependency_resolution"][module] = sorted(map(str, actual))
        for module in TARGETS:
            source = package / "lean" / (module.replace(".", "/") + ".lean")
            quiet(*run("file-check-" + module, ["env", "lean", str(source)]))
        stdout, stderr = run("axioms", ["env", "lean", str(audit)])
        quiet(stdout, stderr)
        report["audit"] = audit_rows(stdout, audit_api)
        report["audit_freshly_elaborated"] = True
        runtime_after, stderr = run("runtime-after", ["env", str(python), "-c", probe])
        quiet(runtime_after, stderr)
        require(json.loads(runtime_after) == metadata, "Active runtime/search paths changed")
        artifact_after = fingerprints(artifact_paths, lean_lib)
        write_json(output / "artifacts-after.json", artifact_after)
        require(artifact_after == artifact_before, "Consumed artifacts changed during validation")
        after = identity_snapshot(api)
        write_json(output / "sources-after.json", after)
        require(after == before, "Original input bytes or native pins changed")
        frozen_after = native.source_files(package)
        write_json(output / "frozen-inputs-after.json", frozen_after)
        require(frozen_after == frozen_before, "Frozen source/config/audit inputs changed")
        report["status"] = "passed"
    except BaseException as error:
        report["error"] = repr(error)
        (output / "failure.log").write_text(traceback.format_exc())
        raise
    finally:
        report["finished_utc"] = datetime.now(timezone.utc).isoformat()
        report["source_snapshot_sha256"] = object_sha(before) if before is not None else None
        if report["status"] != "passed":
            try:
                write_json(output / "sources-final.json", identity_snapshot(api))
            except BaseException as error:
                report["final_source_snapshot_error"] = repr(error)
        if package.exists():
            try:
                write_json(output / "frozen-inputs-final.json", native.source_files(package))
            except BaseException as error:
                report["final_frozen_snapshot_error"] = repr(error)
        write_json(output / "receipt.json", report)
        write_json(output / "evidence-sha256.json", {p.name: sha(p) for p in sorted(output.iterdir())
                   if p.is_file() and p.name != "evidence-sha256.json"})
    return report


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--wait-for-build-lock", action="store_true")
    parser.add_argument("--lake", default="lake")
    parser.add_argument("--output", type=Path, help="New directory below .git/twistor-null-projector/checks")
    args = parser.parse_args()
    output = args.output or OUTPUT_ROOT / (datetime.now(timezone.utc).strftime("%Y%m%dT%H%M%SZ-") + uuid.uuid4().hex[:8])
    api = helpers()
    locks = api[0]
    with locks.BuildLock(locks.DEFAULT_BUILD_LOCK_PATH, "twistor-null-projector-check",
                         block=args.wait_for_build_lock) as lock:
        report = verify_under_lock(lock, output, lake_command=args.lake)
    print(json.dumps({"status": report["status"], "receipt": str(output / "receipt.json"),
                      "audit": report.get("audit", {}).get("module_counts")}, indent=2), flush=True)


if __name__ == "__main__":
    try:
        main()
    except KeyboardInterrupt:
        raise SystemExit(130)
    except (RuntimeError, ValueError, OSError, subprocess.SubprocessError) as error:
        print(str(error), file=sys.stderr)
        raise SystemExit(1)
