#!/usr/bin/env python3
"""Verify the Dzhunushaliev/Myung owners using the existing locked package.

The package and its dependency pins are reused unchanged. Compilation, a
bounded source inventory, forbidden-proof scan, and declaration axiom audit
are separate checks. This does not certify the whole repository.
"""

from __future__ import annotations

import argparse
import hashlib
import importlib.util
import json
from pathlib import Path
import subprocess
import sys

ROOT = Path(__file__).resolve().parents[2]
FOCUSED = ROOT / "verification/real-matrix-split"
OWNERS = (
    "InfoGeometry.Algebra.AkivisIdentity",
    "InfoGeometry.Algebra.NonAssociativeMyung",
    "InfoGeometry.Algebra.DzhunushalievTableAudit",
    "InfoGeometry.Canonical.CanonicalZornNonUnitalNonAssocRing",
    "InfoGeometry.Canonical.DzhunushalievZorn",
    "InfoGeometry.NCG.ZornCommutator",
)
REGRESSION = "InfoGeometry.Lie.CanonicalZornNativeDerivationBridge"


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--output-dir", type=Path)
    args = parser.parse_args()
    output = (args.output_dir or ROOT / "artifacts/verification/dzhunushaliev").resolve()
    output.mkdir(parents=True, exist_ok=True)
    report_path = output / "verification.json"
    report_path.write_text(json.dumps({
        "status": "incomplete", "note": "This run has not passed all checks."
    }, indent=2) + "\n", encoding="utf-8")

    spec = importlib.util.spec_from_file_location("matrix_split_audit", FOCUSED / "audit.py")
    assert spec is not None and spec.loader is not None
    audit = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(audit)
    audit.check_pins(FOCUSED)
    sources = [ROOT / "lean" / (owner.replace(".", "/") + ".lean") for owner in OWNERS]
    before = {str(p.relative_to(ROOT)): hashlib.sha256(p.read_bytes()).hexdigest()
              for p in sources}
    names = [name for owner in OWNERS for name in audit.owner_declarations(owner)]
    expected = set(names)
    if len(expected) != len(names):
        raise SystemExit("Duplicate declaration in the bounded inventory")

    records = []

    def run(label: str, command: list[str]) -> str:
        print(f"[{label}] {' '.join(command)}", flush=True)
        result = subprocess.run(command, cwd=ROOT, text=True,
                                stdout=subprocess.PIPE, stderr=subprocess.STDOUT)
        (output / f"{label}.log").write_text(result.stdout, encoding="utf-8")
        records.append({"label": label, "command": command, "exit": result.returncode})
        print(result.stdout, end="", flush=True)
        if result.returncode:
            raise SystemExit(result.returncode)
        return result.stdout

    audit_file = output / "DeclarationAxioms.lean"
    audit_file.write_text(
        "/-\nCopyright (c) 2026 InfoGeometry Authors. All rights reserved.\n"
        "Released under Apache 2.0 license as described in the file LICENSE.\n"
        "Authors: InfoGeometry Engine Contributors\n-/\n" +
        "\n".join(f"import {owner}" for owner in OWNERS) + "\n\n" +
        "\n".join(f"#print axioms {name}" for name in sorted(expected)) + "\n",
        encoding="utf-8")
    kernel_commands = [
        {"label": "build", "command": ["lake", "-d", str(FOCUSED), "build", *OWNERS, REGRESSION]},
        *({"label": source.stem, "command": ["lean", "-DwarningAsError=true", str(source)]}
          for source in sources),
        {"label": "axioms", "command": ["lean", "-DwarningAsError=true", str(audit_file)]},
    ]
    worker = output / "kernel_worker.py"
    # This private run artifact is launched only beneath the maintained locking
    # wrapper. Its serial children inherit that wrapper's process group; no
    # nested lock acquisition or detached compiler process is introduced.
    worker.write_text(
        "from pathlib import Path\nimport json\nimport subprocess\n"
        f"ROOT = Path({str(ROOT)!r})\nOUTPUT = Path({str(output)!r})\n"
        f"COMMANDS = {kernel_commands!r}\n"
        "records = []\n"
        "receipt = OUTPUT / 'kernel_commands.json'\n"
        "receipt.write_text('[]\\n', encoding='utf-8')\n"
        "for entry in COMMANDS:\n"
        "    print('[' + entry['label'] + '] ' + ' '.join(entry['command']), flush=True)\n"
        "    result = subprocess.run(entry['command'], cwd=ROOT, text=True, shell=False,\n"
        "                            stdout=subprocess.PIPE, stderr=subprocess.STDOUT)\n"
        "    (OUTPUT / (entry['label'] + '.log')).write_text(result.stdout, encoding='utf-8')\n"
        "    records.append({**entry, 'exit': result.returncode})\n"
        "    receipt.write_text(json.dumps(records, indent=2) + '\\n', encoding='utf-8')\n"
        "    print(result.stdout, end='', flush=True)\n"
        "    if result.returncode:\n"
        "        raise SystemExit(result.returncode)\n",
        encoding="utf-8")
    wrapper = [sys.executable, str(FOCUSED / "check.py")]
    run("kernel-batch", [*wrapper, "env", sys.executable, str(worker)])
    kernel_records = json.loads((output / "kernel_commands.json").read_text(encoding="utf-8"))
    if kernel_records != [{**entry, "exit": 0} for entry in kernel_commands]:
        raise SystemExit("The locked compiler batch did not complete the exact command plan")
    log = (output / "axioms.log").read_text(encoding="utf-8")
    audit.check_axioms(log, expected)
    paths = [str(p.relative_to(ROOT)) for p in sources]
    run("screener", [sys.executable, "tools/infra/opengauss_screener.py", *paths, "--strict"])
    run("refute", [sys.executable, "tools/infra/opengauss_cli.py", "refute", *paths, "--strict"])
    run("gate4-static", [sys.executable, "tools/infra/opengauss_cli.py", "review", *paths,
                         "--gate", "GATE_4"])
    run("semantic", [sys.executable, "tools/quality/semantic_vacuity_gate.py", *paths,
                      "--fail-on", "error"])
    after = {str(p.relative_to(ROOT)): hashlib.sha256(p.read_bytes()).hexdigest()
             for p in sources}
    if before != after:
        raise SystemExit("Source changed during verification")
    report = {
        "status": "passed",
        "head": subprocess.check_output(["git", "rev-parse", "HEAD"], cwd=ROOT,
                                        text=True).strip(),
        "lean": subprocess.check_output(["lean", "--version"], cwd=ROOT, text=True).strip(),
        "source_sha256": after,
        "public_declarations_audited": len(expected),
        "commands": records,
        "kernel_commands": kernel_records,
        "regression_target": REGRESSION,
        "scope": "Six selected owners, one real-consumer regression, and their imports "
                 "in the existing focused package; "
                 "not a root-package or repository-wide build",
    }
    report_path.write_text(json.dumps(report, indent=2) + "\n", encoding="utf-8")
    print(f"PASS: {len(expected)} explicitly named public declarations", flush=True)


if __name__ == "__main__":
    main()
