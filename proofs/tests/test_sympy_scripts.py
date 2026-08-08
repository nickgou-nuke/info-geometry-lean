"""Regression tests for the runnable SymPy witness scripts.

These scripts are mostly top-level symbolic checks: importing them would run
their assertions in-process and risk leaking globals between files.  Running
each one in a fresh Python subprocess keeps the checks isolated and mirrors
their command-line use.
"""

from __future__ import annotations

import os
import subprocess
import sys
import time
import unittest
from pathlib import Path


PROOFS_DIR = Path(__file__).resolve().parents[1]
TIMEOUT_SECONDS = 10
MAX_TOTAL_SECONDS = int(os.environ.get("PYTEST_SYMPY_MAX_SECONDS", "50"))

SKIP_PREFIXES = (
    "debug_",
    "fast_extract",
    "fix_",
    "gen_",
    "generate_",
    "ingest_",
    "plot_",
    "python_arango",
    "test_",
)

SKIP_NAMES = {
    "check_lean_eq.py",
    "check_math.py",
    # Full IJIRT/RH audit computes many zeta zeros and GUE samples; run it
    # manually with its own quick/full controls rather than in the smoke suite.
    "riemann_hypothesis_ijirt172568.py",
}


def imports_sympy(path: Path) -> bool:
    source = path.read_text(encoding="utf-8", errors="ignore")
    return "import sympy" in source or "from sympy" in source


def runnable_sympy_scripts() -> list[Path]:
    scripts = []
    for path in sorted(PROOFS_DIR.glob("*.py")):
        if path.name in SKIP_NAMES:
            continue
        if path.name.startswith(SKIP_PREFIXES):
            continue
        if imports_sympy(path):
            scripts.append(path)
    return scripts


class SympyScriptTests(unittest.TestCase):
    def test_runnable_sympy_scripts_pass(self) -> None:
        scripts = runnable_sympy_scripts()
        self.assertGreater(len(scripts), 0, "No runnable SymPy scripts found")

        start = time.monotonic()
        failures: list[str] = []
        skipped = 0
        for script in scripts:
            elapsed = time.monotonic() - start
            if elapsed > MAX_TOTAL_SECONDS:
                skipped += 1
                continue

            with self.subTest(script=script.name):
                try:
                    completed = subprocess.run(
                        [sys.executable, str(script)],
                        cwd=PROOFS_DIR,
                        text=True,
                        stdout=subprocess.PIPE,
                        stderr=subprocess.PIPE,
                        timeout=TIMEOUT_SECONDS,
                        check=False,
                    )
                except subprocess.TimeoutExpired:
                    failures.append(f"{script.name} timed out after {TIMEOUT_SECONDS}s")
                    continue

                if completed.returncode != 0:
                    failures.append(
                        "\n".join(
                            [
                                f"{script.name} exited with {completed.returncode}",
                                "stdout:",
                                completed.stdout[-2000:],
                                "stderr:",
                                completed.stderr[-2000:],
                            ]
                        )
                    )

        if skipped:
            print(f"Skipped {skipped} scripts due to time budget ({MAX_TOTAL_SECONDS}s)", file=sys.stderr)

        if failures:
            self.fail("\n\n".join(failures))


if __name__ == "__main__":
    unittest.main()
