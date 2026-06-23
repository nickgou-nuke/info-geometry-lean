#!/usr/bin/env python3
# -*- coding: utf-8 -*-
"""
Regression test: verify functorial bridge idempotency.

This test exercises the bridge through its CLI entrypoint (the same path used in
manual verification), runs it twice against the same database, and asserts that
reported collection counts remain unchanged after the second run.

Preferred mode:
- create a scratch database (requires Arango _system DB privileges)

Fallback mode:
- only when --allow-shared-db-fallback is provided, run against the existing
  configured database (typically infogeometry)
"""

from __future__ import annotations

import argparse
import os
import re
import subprocess
import sys
import time
from pathlib import Path
from typing import Dict

REPO_ROOT = Path(__file__).resolve().parents[3]
if str(REPO_ROOT) not in sys.path:
    sys.path.insert(0, str(REPO_ROOT))

from tools.infra.arango_env import (  # type: ignore
    arango_database,
    arango_endpoint,
    arango_password,
    arango_username,
    load_repo_arango_env,
)

BRIDGE_SCRIPT = REPO_ROOT / "tools" / "infra" / "aql" / "aql_functorial_bridge.py"
COUNT_LINE = re.compile(r"^(.*?):\s+(\d+)\s*$")
EXPECTED_KEYS = [
    "Mersenne Primes (Discrete)",
    "p-adic Valuations (Discrete)",
    "Golden Powers (Discrete)",
    "Clifford Algebras (Continuous)",
    "Krein Spaces (Continuous)",
    "Hestenes Rotors (Continuous)",
    "Functorial Mappings",
    "Anomaly Resolutions",
]


def parse_args() -> argparse.Namespace:
    load_repo_arango_env(REPO_ROOT)
    p = argparse.ArgumentParser(description="Verify bridge idempotency by running it twice")
    p.add_argument("--database", help="Database to use. If omitted, try scratch DB first.")
    p.add_argument(
        "--allow-shared-db-fallback",
        action="store_true",
        help="If scratch DB creation fails, fall back to configured shared DB and still run the test.",
    )
    p.add_argument("--timeout", type=int, default=180, help="Per bridge invocation timeout in seconds")
    return p.parse_args()


def bridge_env(db_name: str) -> Dict[str, str]:
    env = os.environ.copy()
    env.setdefault("ARANGO_ENDPOINT", arango_endpoint())
    env.setdefault("ARANGO_USER", arango_username())
    env.setdefault("ARANGO_USERNAME", arango_username())
    env.setdefault("ARANGO_PASS", arango_password())
    env.setdefault("ARANGO_PASSWORD", arango_password())
    env["ARANGO_DB"] = db_name
    env["ARANGO_DATABASE"] = db_name
    return env


def run_bridge(args: list[str], env: Dict[str, str], timeout: int) -> subprocess.CompletedProcess[str]:
    return subprocess.run(
        [sys.executable, str(BRIDGE_SCRIPT), *args],
        cwd=str(REPO_ROOT),
        env=env,
        text=True,
        capture_output=True,
        timeout=timeout,
    )


def parse_summary_counts(stdout: str) -> Dict[str, int]:
    counts: Dict[str, int] = {}
    for raw in stdout.splitlines():
        line = raw.rstrip()
        m = COUNT_LINE.match(line)
        if not m:
            continue
        key = m.group(1).rstrip()
        if key in EXPECTED_KEYS:
            counts[key] = int(m.group(2))
    missing = [k for k in EXPECTED_KEYS if k not in counts]
    if missing:
        raise ValueError(f"Missing summary keys: {missing}")
    return counts


def create_scratch_database(db_name: str) -> bool:
    try:
        from arango.client import ArangoClient

        client = ArangoClient(hosts=arango_endpoint())
        sys_db = client.db(
            "_system",
            username=arango_username(),
            password=arango_password(),
        )
        if sys_db.has_database(db_name):
            sys_db.delete_database(db_name)
        sys_db.create_database(db_name)
        return True
    except Exception:
        return False


def drop_database(db_name: str) -> None:
    from arango.client import ArangoClient

    client = ArangoClient(hosts=arango_endpoint())
    sys_db = client.db(
        "_system",
        username=arango_username(),
        password=arango_password(),
    )
    if sys_db.has_database(db_name):
        sys_db.delete_database(db_name)


def print_counts(label: str, counts: Dict[str, int]) -> None:
    print(f"\n=== {label} ===")
    for key in EXPECTED_KEYS:
        print(f"  {key:36s}: {counts[key]:3d}")


def main() -> int:
    args = parse_args()

    print("=" * 70)
    print("FUNCTORIAL BRIDGE IDEMPOTENCY REGRESSION TEST")
    print("=" * 70)

    cleanup_db = False
    if args.database:
        db_name = args.database
        print(f"\nUsing explicitly requested database: {db_name}")
    else:
        scratch = f"infogeometry_bridge_test_{int(time.time())}"
        print(f"\nAttempting scratch database: {scratch}")
        if create_scratch_database(scratch):
            db_name = scratch
            cleanup_db = True
            print(f"✓ Created scratch database: {db_name}")
        else:
            shared = arango_database()
            if not args.allow_shared_db_fallback:
                print("- SKIP: could not create scratch database and shared fallback not allowed")
                print(f"  Configured shared database would be: {shared}")
                return 0
            db_name = shared
            print(f"⚠ Falling back to shared database: {db_name}")

    env = bridge_env(db_name)

    try:
        print("\n----------------------------------------------------------------------")
        print("RUN 1: full bridge")
        print("----------------------------------------------------------------------")
        run1 = run_bridge(["--database", db_name, "--full-bridge"], env, args.timeout)
        print(run1.stdout)
        if run1.returncode != 0:
            print(run1.stderr)
            print(f"✗ Run 1 failed with exit code {run1.returncode}")
            return 1

        summary1 = run_bridge(["--database", db_name, "--summary"], env, args.timeout)
        print(summary1.stdout)
        if summary1.returncode != 0:
            print(summary1.stderr)
            print(f"✗ Summary after run 1 failed with exit code {summary1.returncode}")
            return 1
        counts1 = parse_summary_counts(summary1.stdout)
        print_counts("After Run 1", counts1)

        print("\n----------------------------------------------------------------------")
        print("RUN 2: full bridge again")
        print("----------------------------------------------------------------------")
        run2 = run_bridge(["--database", db_name, "--full-bridge"], env, args.timeout)
        print(run2.stdout)
        if run2.returncode != 0:
            print(run2.stderr)
            print(f"✗ Run 2 failed with exit code {run2.returncode}")
            return 1

        summary2 = run_bridge(["--database", db_name, "--summary"], env, args.timeout)
        print(summary2.stdout)
        if summary2.returncode != 0:
            print(summary2.stderr)
            print(f"✗ Summary after run 2 failed with exit code {summary2.returncode}")
            return 1
        counts2 = parse_summary_counts(summary2.stdout)
        print_counts("After Run 2", counts2)

        print("\n----------------------------------------------------------------------")
        print("VERIFICATION")
        print("----------------------------------------------------------------------")
        ok = True
        for key in EXPECTED_KEYS:
            c1 = counts1[key]
            c2 = counts2[key]
            delta = c2 - c1
            if c1 == c2:
                print(f"  ✓ PASS {key:36s}: {c1:3d} → {c2:3d} (Δ={delta:+d})")
            else:
                ok = False
                print(f"  ✗ FAIL {key:36s}: {c1:3d} → {c2:3d} (Δ={delta:+d})")

        print("\n" + "=" * 70)
        if ok:
            print("✓ IDEMPOTENCY TEST PASSED")
            print("  All summary counts remained stable across two runs.")
        else:
            print("✗ IDEMPOTENCY TEST FAILED")
            print("  Some summary counts changed across runs.")
        print("=" * 70)
        return 0 if ok else 1
    finally:
        if cleanup_db:
            print(f"\nCleaning up scratch database: {db_name}")
            try:
                drop_database(db_name)
                print(f"✓ Database {db_name} dropped")
            except Exception as e:
                print(f"⚠ Warning: could not drop scratch database {db_name}: {e}")


if __name__ == "__main__":
    raise SystemExit(main())
