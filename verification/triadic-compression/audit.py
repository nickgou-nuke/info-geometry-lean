#!/usr/bin/env python3
"""Export a fresh native audit of nine selected owners, not a repository gate.

Invoke directly after committing the implementation. Each check.py subprocess
owns the shared build lock; do not wrap this driver in check.py itself.
"""

from __future__ import annotations

import argparse
from collections import Counter
from datetime import datetime, timezone
import hashlib
import heapq
import json
from pathlib import Path
import re
import signal
import subprocess
import sys
import time
import tomllib

PROJECT = Path(__file__).resolve().parent
ROOT = PROJECT.parents[1]
LOGS = PROJECT / "logs"
OWNERS = (
    "InfoGeometry.Physics.Algebra.TripotentPeirceProjectors",
    "InfoGeometry.Core.PeirceDecomposition",
    "InfoGeometry.Core.PeirceCompressionDefect",
    "InfoGeometry.Core.PeirceCompressionCStar",
    "InfoGeometry.Core.CornerCentrality",
    "InfoGeometry.Core.TripotentCompression",
    "InfoGeometry.Core.TripotentCompressionCStar",
    "InfoGeometry.Core.TripotentCompressionHilbert",
    "InfoGeometry.OperatorAlgebra.TriadicCompressionCounterexample",
)
AUDIT = "lean/InfoGeometry/Core/TripotentCompressionAudit.lean"
PROTECTED = ["lean/" + owner.replace(".", "/") + ".lean" for owner in OWNERS] + [AUDIT] + [
    "verification/triadic-compression/" + name for name in
    ("check.py", "audit.py", "lakefile.toml", "lake-manifest.json", "lean-toolchain")
] + ["lean-toolchain", "lake-manifest.json", "lakefile.lean", "lakefile.toml",
     "tools/build_lock.py", "tools/infra/build.py"]
ALLOWED = {"propext", "Classical.choice", "Quot.sound"}
MATHLIB_PIN = "d13f23b723b8a846827a245b89c10fc7d3f11612"
EXPECTED_EDGES = {
    ("InfoGeometry.Core.PeirceCompressionDefect.compression_mul_defect",
     "InfoGeometry.Core.TripotentCompression.compression_mul_defect_two_channels"),
    ("InfoGeometry.Core.TripotentCompression.idempotent_compression_defect_eq_gram_sum",
     "InfoGeometry.Core.TripotentCompressionHilbert.inner_compression_defect"),
}
PREFIX = "TRIADIC_COMPRESSION_"


def require(condition: bool, message: str) -> None:
    if not condition:
        raise RuntimeError(message)


def digest(data: bytes) -> str:
    return hashlib.sha256(data).hexdigest()


def git(*args: str, cwd: Path = ROOT) -> str:
    return subprocess.check_output(["git", *args], cwd=cwd, text=True,
                                   stderr=subprocess.PIPE).strip()


def snapshot(head: str) -> dict:
    hashes = {}
    for path in PROTECTED:
        data = (ROOT / path).read_bytes()
        committed = subprocess.check_output(["git", "show", head + ":" + path],
                                            cwd=ROOT, stderr=subprocess.PIPE)
        require(data == committed, "Source differs from committed bytes: " + path)
        hashes[path] = digest(data)
    return hashes


def pins() -> dict:
    toolchain = (PROJECT / "lean-toolchain").read_bytes()
    require(toolchain == (ROOT / "lean-toolchain").read_bytes(), "Toolchain differs from root")
    focused = json.loads((PROJECT / "lake-manifest.json").read_text())
    root = json.loads((ROOT / "lake-manifest.json").read_text())
    root_pins = {p["name"]: p["rev"] for p in root["packages"] if p["type"] == "git"}
    config = tomllib.loads((PROJECT / "lakefile.toml").read_text())
    math = [p for p in config["require"] if p["name"] == "mathlib"]
    require(len(math) == 1 and math[0]["rev"] == MATHLIB_PIN, "Unexpected mathlib config pin")
    revisions = {}
    for package in focused["packages"]:
        name, revision = package["name"], package["rev"]
        path = (PROJECT / focused["packagesDir"] / name).resolve()
        require(package["type"] == "git" and name not in revisions, "Invalid dependency entry")
        require(root_pins.get(name) == revision == git("rev-parse", "HEAD", cwd=path),
                "Dependency revision mismatch: " + name)
        require(not git("status", "--porcelain=v1", "--untracked-files=no", cwd=path),
                "Tracked dependency changes: " + name)
        revisions[name] = revision
    require(revisions.get("mathlib") == MATHLIB_PIN, "Unexpected mathlib manifest or checkout")
    return {"toolchain": toolchain.decode().strip(), "revisions": revisions, "tracked_clean": True}


def parse_audit(raw: str) -> dict:
    require(PREFIX + "AUDIT_FAILURE:" not in raw, "Native audit reported failure")
    finals = re.findall(PREFIX + r"AUDIT_PASS: (\d+) declarations, (\d+) theorem declarations", raw)
    require(len(finals) == raw.count(PREFIX + "AUDIT_PASS:") == 1, "Expected exactly one PASS marker")
    rows = re.findall(PREFIX + r"DECL: (\S+): ([^:\n]+): (#?\[[^\]]*\])", raw)
    declarations = []
    for owner, name, axioms_raw in rows:
        axioms = [a.strip().lstrip("`") for a in axioms_raw.lstrip("#")[1:-1].split(",") if a.strip()]
        require(set(axioms) <= ALLOWED and len(axioms) == len(set(axioms)), "Invalid axiom inventory")
        declarations.append({"owner": owner, "name": name.strip(), "axioms": sorted(axioms)})
    count, theorem_count = map(int, finals[0])
    names = {d["name"] for d in declarations}
    require(count == len(declarations) == len(names) == raw.count(PREFIX + "DECL:"),
            "Incomplete or duplicated declaration enumeration")
    require(0 < theorem_count <= count, "Invalid native theorem count")
    owner_rows = re.findall(PREFIX + r"OWNER: (\S+): (\d+)", raw)
    owner_counts = dict(Counter(d["owner"] for d in declarations))
    require(len(owner_rows) == raw.count(PREFIX + "OWNER:") == len(OWNERS) and
            len({o for o, _ in owner_rows}) == len(OWNERS) and
            set(owner_counts) == set(OWNERS) and
            {o: int(n) for o, n in owner_rows} == owner_counts, "Nine-owner inventory mismatch")
    edge_rows = re.findall(PREFIX + r"EDGE: ([^\n]+?) -> ([^\n]+)", raw)
    edges = {(source.strip(), target.strip()) for source, target in edge_rows}
    require(len(edges) == len(edge_rows) == raw.count(PREFIX + "EDGE:"), "Invalid or repeated EDGE marker")
    require(all(a in names and b in names for a, b in edges), "EDGE endpoint outside audited declarations")
    require(EXPECTED_EDGES <= edges, "Missing proof-body dependency: check value? (allowOpaque := true)")
    successors, indegree = {n: set() for n in names}, dict.fromkeys(names, 0)
    for source, target in edges:
        successors[source].add(target)
        indegree[target] += 1
    ready, order = [n for n in names if indegree[n] == 0], []
    heapq.heapify(ready)
    while ready:
        node = heapq.heappop(ready)
        order.append(node)
        for target in sorted(successors[node]):
            indegree[target] -= 1
            if indegree[target] == 0:
                heapq.heappush(ready, target)
    require(len(order) == len(names), "Native declaration dependencies contain a cycle")
    usage = Counter(a for d in declarations for a in d["axioms"])
    return {"declaration_count": count, "theorem_declaration_count": theorem_count,
            "owner_counts": owner_counts, "allowed_axioms": sorted(ALLOWED),
            "axiom_usage_counts": {a: usage[a] for a in sorted(ALLOWED)},
            "declarations": sorted(declarations, key=lambda d: d["name"]),
            "edge_origin": "native declaration types and proof/definition values; selected-owner induced graph",
            "edge_direction": "dependency -> dependent", "edge_count": len(edges),
            "edges": [{"dependency": a, "dependent": b} for a, b in sorted(edges)],
            "topological_order": order, "expected_proof_edges_observed": True}


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--output", type=Path, default=LOGS / "validation.json")
    output = parser.parse_args().output.resolve()
    stamp = datetime.now(timezone.utc).strftime("%Y%m%dT%H%M%S.%fZ")
    report = {"schema": "triadic-compression-native-audit-v1", "status": "RUNNING",
              "started_utc": datetime.now(timezone.utc).isoformat(), "selected_owners": list(OWNERS),
              "scope_exclusions": ["whole repository build", "publication acceptance", "physical interpretation"],
              "independent_qa_acceptance": False, "commands": []}

    def run(label: str, args: list[str]) -> str:
        argv = [sys.executable, str(PROJECT / "check.py"), *args]
        out, err = (LOGS / f"{stamp}-{label}.{stream}.log" for stream in ("stdout", "stderr"))
        entry = {"argv": argv, "stdout_log": str(out), "stderr_log": str(err)}
        report["commands"].append(entry)
        start = time.monotonic()
        print("CHECK_START", label, flush=True)
        try:
            with out.open("wb") as stdout, err.open("wb") as stderr:
                process = subprocess.Popen(argv, cwd=ROOT, stdout=stdout, stderr=stderr,
                                           start_new_session=True)
                try:
                    entry["exit_code"] = process.wait()
                except KeyboardInterrupt:
                    process.send_signal(signal.SIGINT)
                    entry["exit_code"] = process.wait()
                    raise
        finally:
            entry["duration_seconds"] = round(time.monotonic() - start, 3)
            for stream, path in (("stdout", out), ("stderr", err)):
                if path.exists():
                    entry[stream + "_sha256"] = digest(path.read_bytes())
        require(entry["exit_code"] == 0, label + " failed; see captured logs")
        print("CHECK_END", label, entry["exit_code"], flush=True)
        return out.read_text() + "\n" + err.read_text()

    try:
        LOGS.mkdir(parents=True, exist_ok=True)
        head = git("rev-parse", "HEAD")
        report.update(implementation_commit=head, git_tree=git("rev-parse", "HEAD^{tree}"))
        report["source_sha256_before"] = snapshot(head)
        report["pins_before"] = pins()
        run("focused-build", ["build", "InfoGeometry.Core.TripotentCompressionAudit"])
        report["audit"] = parse_audit(run("fresh-audit", ["env", "lean", str(ROOT / AUDIT)]))
        report["source_sha256_after"] = snapshot(head)
        report["pins_after"] = pins()
        report["git_head_after"] = git("rev-parse", "HEAD")
        require(report["git_head_after"] == head, "Implementation HEAD changed during audit")
        require(report["source_sha256_before"] == report["source_sha256_after"] and
                report["pins_before"] == report["pins_after"], "Sources or pins changed during audit")
        report["status"] = "PASSED"
    except (Exception, KeyboardInterrupt) as error:
        report.update(status="FAILED", failure=type(error).__name__ + ": " + str(error))
        print(report["failure"], file=sys.stderr)
    report["finished_utc"] = datetime.now(timezone.utc).isoformat()
    output.parent.mkdir(parents=True, exist_ok=True)
    output.write_text(json.dumps(report, indent=2, sort_keys=True) + "\n")
    print(report["status"], output, flush=True)
    return 0 if report["status"] == "PASSED" else 1


if __name__ == "__main__":
    raise SystemExit(main())
