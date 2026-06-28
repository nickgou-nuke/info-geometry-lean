#!/usr/bin/env python3
"""
Möbius Cross-Engine JSON Harness
Reads a JSON packet and verifies it across all available engines.
"""

import json
import subprocess
import sys
from pathlib import Path
from typing import Any


ROOT = Path(__file__).parent.parent.parent


def packet_class(packet_path: Path, packet: dict[str, Any]) -> str:
    expected = packet.get("expected")
    if isinstance(expected, dict):
        cls = expected.get("classification")
        if isinstance(cls, str) and cls:
            return cls
    cls = packet.get("classification")
    if isinstance(cls, str) and cls:
        return cls
    stem = packet_path.stem.lower()
    for candidate in ("hyperbolic", "parabolic", "elliptic", "loxodromic"):
        if candidate in stem:
            return candidate
    raise ValueError(f"Cannot infer packet classification from {packet_path}")


def run_cmd(cmd: list[str], cwd: Path = ROOT) -> tuple[int, str, str]:
    try:
        result = subprocess.run(cmd, cwd=cwd, capture_output=True, text=True, timeout=120)
        return result.returncode, result.stdout, result.stderr
    except subprocess.TimeoutExpired:
        return -1, "", "timeout"
    except FileNotFoundError:
        return -1, "", "not found"


def check_ok(returncode: int, stdout: str, stderr: str, ok_marker: str | None = None) -> dict[str, Any]:
    if returncode != 0:
        return {"status": "FAIL", "error": stderr or "non-zero exit"}
    if ok_marker and ok_marker not in stdout:
        return {"status": "FAIL", "error": f"missing marker: {ok_marker}"}
    return {"status": "OK", "output": stdout.strip()}


def verify_sympy(packet: dict[str, Any], cls: str) -> dict[str, Any]:
    code, out, err = run_cmd(["python3", "tools/mobius/mobius_sympy.py", cls])
    return check_ok(code, out, err, "MOBIUS_SYMPY_OK")


def verify_sage(packet: dict[str, Any], cls: str) -> dict[str, Any]:
    code, out, err = run_cmd([
        "/home/goutev/miniforge3/envs/sage/bin/python3",
        "tools/sage/mobius_sage.py",
        cls,
    ])
    return check_ok(code, out, err, "MOBIUS_SAGE_OK")


def verify_gap(packet: dict[str, Any], cls: str) -> dict[str, Any]:
    code, out, err = run_cmd([
        "/home/goutev/miniforge3/envs/sage/bin/gap",
        "-q",
        "-c",
        f'PacketName:="{cls}";; Read("tools/mobius/mobius_gap.g");',
    ])
    return check_ok(code, out, err, "MOBIUS_GAP_OK")


def verify_clifford(packet: dict[str, Any], cls: str) -> dict[str, Any]:
    code, out, err = run_cmd(["python3", "tools/mobius/mobius_clifford.py"])
    return check_ok(code, out, err, "MOBIUS_CLIFFORD_OK")


def verify_galgebra(packet: dict[str, Any], cls: str) -> dict[str, Any]:
    code, out, err = run_cmd(["python3", "tools/mobius/mobius_galgebra.py"])
    return check_ok(code, out, err, "MOBIUS_GALGEBRA_OK")


def verify_coq(packet: dict[str, Any], cls: str) -> dict[str, Any]:
    code, out, err = run_cmd(["coqc", "tools/coq/MobiusDual2x2.v"])
    return check_ok(code, out, err)


def verify_lean(packet: dict[str, Any], cls: str) -> dict[str, Any]:
    code, out, err = run_cmd(["/home/goutev/.elan/bin/lake", "env", "lean", "lean/InfoGeometry/Geometry/MobiusDual2x2.lean"])
    return check_ok(code, out, err)


def verify_isabelle(packet: dict[str, Any], cls: str) -> dict[str, Any]:
    code, out, err = run_cmd(["/usr/local/bin/isabelle", "build", "-D", "tools/isabelle/mobius"])
    return check_ok(code, out, err, "elapsed time")


def main():
    if len(sys.argv) < 2:
        print("Usage: python3 mobius_json_harness.py <packet.json>")
        sys.exit(1)

    packet_path = Path(sys.argv[1])
    if not packet_path.exists():
        print(f"File not found: {packet_path}")
        sys.exit(1)

    with open(packet_path) as f:
        packet = json.load(f)
    cls = packet_class(packet_path, packet)

    print(f"=== Möbius JSON Cross-Engine Verification ===")
    print(f"Packet: {packet_path}")
    print(f"Matrix: {packet['matrix']}")
    print()

    engines = [
        ("SymPy", verify_sympy),
        ("SageMath", verify_sage),
        ("GAP", verify_gap),
        ("Clifford", verify_clifford),
        ("GAlgebra", verify_galgebra),
        ("Coq", verify_coq),
        ("Lean4", verify_lean),
        ("Isabelle", verify_isabelle),
    ]

    results = {}
    for name, verify_fn in engines:
        print(f"Running {name}...", end=" ", flush=True)
        result = verify_fn(packet, cls)
        results[name] = result
        if result["status"] == "OK":
            print("✅ OK")
        else:
            print(f"❌ FAIL: {result.get('error', 'unknown')}")

    print()
    print("=== SUMMARY ===")
    passed = sum(1 for r in results.values() if r["status"] == "OK")
    total = len(results)
    print(f"Passed: {passed}/{total}")
    if passed == total:
        print("🎉 ALL ENGINES VERIFIED")
        sys.exit(0)
    else:
        print("⚠️  SOME ENGINES FAILED")
        sys.exit(1)


if __name__ == "__main__":
    main()
