#!/usr/bin/env python3
"""Run public spectral-table audits and plots without fetching dependencies.

Repository paths are resolved from this file, independently of the working
directory. All generated files are placed under --output-dir.
"""
from __future__ import annotations

import argparse
import importlib.metadata
import json
from pathlib import Path
import platform
import subprocess
import sys
import time

from fixtures import (DATA_DIR, DEFAULT_OUTPUT_DIR, REPO_ROOT, TOOLS_DIR,
                      public_path, read_reference, read_rounded_fixture, sha)

KERNEL_SHA = "b22d93a4a44ec5e2d2b43c1b7c3d96585f2c76f5aea22b79218602efbacb5784"


def main(output_dir, skip_figure=False):
    output_dir = output_dir.resolve()
    verification = output_dir / "verification"
    verification.mkdir(parents=True, exist_ok=True)
    report_path = verification / "numerical_verification.json"
    report = {
        "status": "running", "no_dependency_fetching": True,
        "output_directory": public_path(output_dir), "jobs": [],
    }
    report_path.write_text(json.dumps(report, indent=2) + "\n")
    try:
        dependencies = {"python": platform.python_version(),
                        "numpy": importlib.metadata.version("numpy")}
        if not skip_figure:
            dependencies["matplotlib"] = importlib.metadata.version("matplotlib")
        report["dependencies"] = dependencies
        kernel = TOOLS_DIR / "audit_exact_two_line_bounds.py"
        if sha(kernel) != KERNEL_SHA:
            raise ValueError("the unchanged interval kernel hash does not match")
        _, _, fixture_provenance = read_rounded_fixture(DATA_DIR / "rounded_two_line.json")
        report["rounded_fixture_provenance"] = fixture_provenance
        jobs = ["audit_spectral_domains.py", "certify_decimal_two_line.py"]
        if not skip_figure:
            jobs.append("plot_spectral_bridge.py")
        for name in jobs:
            script = TOOLS_DIR / name
            before = sha(script)
            start = time.monotonic()
            result = subprocess.run(
                [sys.executable, str(script), "--output-dir", str(output_dir)],
                cwd=REPO_ROOT, text=True, stdout=subprocess.PIPE, stderr=subprocess.STDOUT,
            )
            log = verification / ("numerical_" + script.stem + ".log")
            log.write_text(result.stdout)
            record = {
                "script": public_path(script), "exit_code": result.returncode,
                "seconds": time.monotonic() - start, "script_sha256": sha(script),
                "source_stable": before == sha(script),
                "log": log.relative_to(output_dir).as_posix(),
            }
            report["jobs"].append(record)
            if result.returncode:
                raise RuntimeError(name + " failed; inspect its captured numerical log")
            if not record["source_stable"]:
                raise RuntimeError(name + " changed during reproduction")
            print("PASS", name, flush=True)
        if sha(kernel) != KERNEL_SHA:
            raise ValueError("interval kernel changed during reproduction")
        new = json.loads((output_dir / "results" / "decimal_two_line_certificate.json").read_text())
        old = read_reference(DATA_DIR / "prior_two_line_bounds_audit.json",
                             "prior_two_line_bounds_audit.json")["two_line_bounds"]
        for name in ["M", "delta", "C3", "Cmax"]:
            if new["rounded_source"]["quantities"][name] != old[name]:
                raise ArithmeticError("old interval endpoint reproduction failed: " + name)
        if (new["rounded_source"]["quantities"]["actual_max_centered_quadratic_remainder"]
                != old["actual_max_absolute_quadratic_remainder"]):
            raise ArithmeticError("old remainder interval reproduction failed")
        outputs = list((output_dir / "results").glob("*.json"))
        outputs += list((output_dir / "results").glob("*.csv"))
        if not skip_figure:
            outputs += list((output_dir / "figures").glob("*"))
        report.update({
            "status": "passed", "interval_kernel_sha256": KERNEL_SHA,
            "interval_kernel_unchanged": True,
            "rounded_interval_endpoints_reproduced_exactly": True,
            "runner_sha256": sha(Path(__file__)),
            "outputs": [{"path": p.relative_to(output_dir).as_posix(),
                         "bytes": p.stat().st_size, "sha256": sha(p)}
                        for p in sorted(outputs) if p.is_file()],
        })
    except Exception as error:
        report.update({"status": "failed", "error": str(error)})
        report_path.write_text(json.dumps(report, indent=2) + "\n")
        raise
    report_path.write_text(json.dumps(report, indent=2) + "\n")
    print("All numerical verification passed.", flush=True)


if __name__ == "__main__":
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--output-dir", type=Path, default=DEFAULT_OUTPUT_DIR)
    parser.add_argument("--skip-figure", action="store_true")
    args = parser.parse_args()
    main(args.output_dir, args.skip_figure)
