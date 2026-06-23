#!/usr/bin/env python3
# -*- coding: utf-8 -*-
"""
Lightweight test entrypoint for info-geometry-lean tools.

Usage:
  python3 tools/test_runner.py [test_name]

Examples:
  # Run all tests
  python3 tools/test_runner.py

  # Run specific test
  python3 tools/test_runner.py bridge_idempotency

  # List available tests
  python3 tools/test_runner.py --list
"""

from __future__ import annotations

import argparse
import os
import subprocess
import sys
from pathlib import Path
from typing import Callable, Dict, List, Tuple

REPO_ROOT = Path(__file__).resolve().parents[1]
TOOLS_INFRA = REPO_ROOT / "tools" / "infra"


class TestSpec:
    def __init__(self, name: str, description: str, command: List[str], cwd: Path = REPO_ROOT):
        self.name = name
        self.description = description
        self.command = command
        self.cwd = cwd

    def run(self, timeout: int = 300) -> Tuple[bool, str]:
        try:
            result = subprocess.run(
                [sys.executable, *self.command],
                cwd=str(self.cwd),
                text=True,
                capture_output=True,
                timeout=timeout,
            )
            output = result.stdout + result.stderr
            success = result.returncode == 0
            return success, output
        except subprocess.TimeoutExpired:
            return False, f"Test timed out after {timeout}s"
        except Exception as e:
            return False, f"Test execution failed: {e}"


TESTS: Dict[str, TestSpec] = {
    "bridge_idempotency": TestSpec(
        name="bridge_idempotency",
        description="Verify functorial bridge idempotency (no duplicate accumulation)",
        command=[
            str(TOOLS_INFRA / "aql" / "test_bridge_idempotency.py"),
            "--allow-shared-db-fallback",
        ],
    ),
    # Add more tests here as they are developed:
    # "dag_coverage": TestSpec(...),
    # "lean_compile": TestSpec(...),
}


def list_tests():
    print("Available tests:\n")
    for name, spec in sorted(TESTS.items()):
        print(f"  {name:25s} - {spec.description}")
    print(f"\nTotal: {len(TESTS)} test(s)")


def run_test(name: str, timeout: int = 300) -> bool:
    if name not in TESTS:
        print(f"✗ Unknown test: {name}")
        print("\nAvailable tests:")
        list_tests()
        return False

    spec = TESTS[name]
    print("=" * 70)
    print(f"Running: {spec.name}")
    print(f"Description: {spec.description}")
    print(f"Command: {' '.join([sys.executable, *spec.command])}")
    print("=" * 70)

    success, output = spec.run(timeout=timeout)

    print(output)

    print("\n" + "=" * 70)
    if success:
        print(f"✓ {spec.name} PASSED")
    else:
        print(f"✗ {spec.name} FAILED")
    print("=" * 70)

    return success


def run_all_tests(timeout: int = 300) -> bool:
    print(f"Running {len(TESTS)} test(s)...\n")

    results: List[Tuple[str, bool]] = []
    for name in sorted(TESTS.keys()):
        success = run_test(name, timeout=timeout)
        results.append((name, success))
        print()

    # Summary
    print("=" * 70)
    print("TEST SUMMARY")
    print("=" * 70)
    for name, success in results:
        status = "✓ PASS" if success else "✗ FAIL"
        print(f"  {status} {name}")

    all_passed = all(success for _, success in results)
    print("\n" + "=" * 70)
    if all_passed:
        print(f"✓ ALL TESTS PASSED ({len(results)}/{len(results)})")
    else:
        failed = sum(1 for _, success in results if not success)
        print(f"✗ {failed}/{len(results)} TEST(S) FAILED")
    print("=" * 70)

    return all_passed


def main() -> int:
    parser = argparse.ArgumentParser(
        description="Lightweight test runner for info-geometry-lean tools"
    )
    parser.add_argument(
        "test_name",
        nargs="?",
        help="Test to run. If omitted, runs all tests.",
    )
    parser.add_argument(
        "--list",
        action="store_true",
        help="List available tests",
    )
    parser.add_argument(
        "--timeout",
        type=int,
        default=300,
        help="Per-test timeout in seconds (default: 300)",
    )
    args = parser.parse_args()

    if args.list:
        list_tests()
        return 0

    if args.test_name:
        success = run_test(args.test_name, timeout=args.timeout)
        return 0 if success else 1
    else:
        all_passed = run_all_tests(timeout=args.timeout)
        return 0 if all_passed else 1


if __name__ == "__main__":
    sys.exit(main())