#!/usr/bin/env python3
"""Check the real direct-limit constructions in the existing pinned, locked Lean package.

Source checks, kernel compilation, and the bounded declaration axiom audit
remain distinct. --source-only never records a kernel verification success.
"""

from __future__ import annotations

import argparse
import hashlib
import importlib.util
import json
import os
from pathlib import Path
import subprocess
import sys

ROOT = Path(__file__).resolve().parents[2]
FOCUSED = ROOT / "verification/zeta-weil-krein"
INVENTORY = ROOT / "verification/real-matrix-split/audit.py"
OWNERS = (
    "InfoGeometry.LinearAlgebra.DirectLimitBilinear",
    "InfoGeometry.LinearAlgebra.DirectLimitEndomorphism",
    "InfoGeometry.LinearAlgebra.DirectLimitPairingOperators",
    "InfoGeometry.LinearAlgebra.DirectLimitRadicalQuotient",
    "InfoGeometry.LinearAlgebra.DirectLimitReflection",
    "InfoGeometry.Arithmetic.FiniteEulerLogDerivative",
    "InfoGeometry.Modular.NativeDirectLimitDerivation",
    "InfoGeometry.Clifford.RealFockInfinityPairing",
)
REGRESSION_TARGETS = (
    "InfoGeometry.Clifford.RealFockHilbertCompletion",
    "InfoGeometry.Arithmetic.ZetaDihedralWeilKreinAudit",
)


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--output-dir", type=Path)
    parser.add_argument("--source-only", action="store_true")
    parser.add_argument("--wait-for-build-lock", action="store_true",
                        help="Wait behind an occupied compiler lock instead of recording a blocked run")
    args = parser.parse_args()
    output = (args.output_dir or ROOT / "artifacts/verification/real-colimit").resolve()
    output.mkdir(parents=True, exist_ok=True)
    report_path = output / "verification.json"
    report_path.write_text(json.dumps({
        "status": "incomplete", "note": "This run has not passed all checks."
    }, indent=2) + "\n", encoding="utf-8")

    spec = importlib.util.spec_from_file_location("matrix_split_audit", INVENTORY)
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
        chunks = []
        with (output / f"{label}.log").open("w", encoding="utf-8") as log:
            process = subprocess.Popen(command, cwd=ROOT, text=True,
                                       stdout=subprocess.PIPE, stderr=subprocess.STDOUT,
                                       start_new_session=(os.name == "posix"))
            try:
                assert process.stdout is not None
                for line in process.stdout:
                    chunks.append(line)
                    log.write(line)
                    log.flush()
                    print(line, end="", flush=True)
                code = process.wait()
            except KeyboardInterrupt:
                # The maintained wrapper handles SIGINT and cleans up its own
                # child process group. Do not signal any other build owner.
                if process.poll() is None:
                    import signal
                    process.send_signal(signal.SIGINT)
                process.wait()
                raise
        records.append({"label": label, "command": command, "exit": code})
        if code:
            raise SystemExit(code)
        return "".join(chunks)

    paths = [str(p.relative_to(ROOT)) for p in sources]
    run("screener", [sys.executable, "tools/infra/opengauss_screener.py", *paths, "--strict"])
    run("refute", [sys.executable, "tools/infra/opengauss_cli.py", "refute", *paths, "--strict"])
    run("gate4-static", [sys.executable, "tools/quality/proof_proxy_staged_gate.py", *paths])
    run("semantic", [sys.executable, "tools/quality/semantic_vacuity_gate.py", *paths,
                      "--fail-on", "error"])
    source_after = {str(p.relative_to(ROOT)): hashlib.sha256(p.read_bytes()).hexdigest()
                    for p in sources}
    if before != source_after:
        raise SystemExit("Source changed during source checks")
    report = {
        "status": "source_checks_passed_kernel_pending",
        "source_sha256": before,
        "public_declarations_inventoried": len(expected),
        "commands": records,
        "scope": "Eight selected lean/ owners and their imports, plus the existing Fock "
                 "completion and finite arithmetic audit as regression targets; "
                 "not a root-package or repository-wide build",
        "toolchain": (ROOT / "lean-toolchain").read_text().strip(),
    }
    report_path.write_text(json.dumps(report, indent=2) + "\n", encoding="utf-8")
    print(f"SOURCE CHECKS ONLY: {len(expected)} public declarations inventoried", flush=True)
    if args.source_only:
        return

    audit_file = output / "DeclarationAxioms.lean"
    audit_file.write_text(
        "/-\nCopyright (c) 2026 InfoGeometry Authors. All rights reserved.\n"
        "Released under Apache 2.0 license as described in the file LICENSE.\n"
        "Authors: InfoGeometry Engine Contributors\n-/\n" +
        "\n".join(f"import {owner}" for owner in OWNERS) + "\n\n" +
        "\n".join(f"#print axioms {name}" for name in sorted(expected)) + "\n",
        encoding="utf-8")
    kernel_commands = [
        {"label": "build", "command": ["lake", "-d", str(FOCUSED), "build", *OWNERS, *REGRESSION_TARGETS]},
        *({"label": source.stem, "command": ["lean", "-DwarningAsError=true", str(source)]}
          for source in sources),
        {"label": "axioms", "command": ["lean", "-DwarningAsError=true", str(audit_file)]},
    ]
    worker = output / "kernel_worker.py"
    # This generated run artifact is launched only beneath the maintained
    # locking wrapper. All compiler commands run serially in that process group.
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
    report["requested_kernel_commands"] = kernel_commands
    report_path.write_text(json.dumps(report, indent=2) + "\n", encoding="utf-8")
    if not args.wait_for_build_lock:
        # This probe only reports availability. It does not authorize or launch
        # any compiler: the maintained wrapper acquires the actual execution lock.
        sys.path.insert(0, str(ROOT))
        from tools.build_lock import BuildLockBusyError, acquire_build_lock
        try:
            probe = acquire_build_lock(None, f"real-colimit-preflight:{os.getpid()}", block=False)
        except BuildLockBusyError as error:
            report.update({"status": "source_checks_passed_kernel_blocked",
                           "blocker": str(error), "lock_metadata": error.metadata})
            report_path.write_text(json.dumps(report, indent=2) + "\n", encoding="utf-8")
            print(f"KERNEL NOT STARTED: {error}", file=sys.stderr, flush=True)
            raise SystemExit(2)
        else:
            probe.release()
    wrapper = [sys.executable, str(FOCUSED / "check.py")]
    (output / "kernel_commands.json").unlink(missing_ok=True)
    run("kernel-batch", [*wrapper, "env", sys.executable, str(worker)])
    kernel_records = json.loads((output / "kernel_commands.json").read_text(encoding="utf-8"))
    if kernel_records != [{**entry, "exit": 0} for entry in kernel_commands]:
        raise SystemExit("The locked compiler batch did not complete the exact command plan")
    audit.check_axioms((output / "axioms.log").read_text(encoding="utf-8"), expected)
    after = {str(p.relative_to(ROOT)): hashlib.sha256(p.read_bytes()).hexdigest()
             for p in sources}
    if before != after:
        raise SystemExit("Source changed during verification")
    report.update({
        "status": "passed",
        "head": subprocess.check_output(["git", "rev-parse", "HEAD"], cwd=ROOT,
                                        text=True).strip(),
        "source_sha256": after,
        "public_declarations_audited": len(expected),
        "commands": records,
        "kernel_commands": kernel_records,
    })
    report_path.write_text(json.dumps(report, indent=2) + "\n", encoding="utf-8")
    print(f"PASS: {len(expected)} explicitly named public declarations", flush=True)


if __name__ == "__main__":
    main()
