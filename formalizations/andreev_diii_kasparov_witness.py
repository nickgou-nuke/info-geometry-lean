#!/usr/bin/env python3
"""Finite 2×2 SymPy witness for the Andreev–DIII–Kasparov bridge.

This script checks:
  - Möbius/DIII time-reversal matrix K = [[0, 1], [-1, 0]]
  - particle-hole / CPT matrix C = diag(1, -1)
  - chiral grading S = K C
  - Andreev finite reflection A = -K = [[0, -1], [1, 0]]
  - Kasparov defect laws for A (transpose as star on this real model)

It can also emit a compact status payload for Lean ingestion:
  `{"schema": ..., "is_verified": true|false, "status": "verified"|"failed"}`.
"""

from __future__ import annotations

import argparse
import json
from pathlib import Path
from sympy import Matrix


def run_checks() -> tuple[bool, str]:
    try:
        K = Matrix([[0, 1], [-1, 0]])
        C = Matrix([[1, 0], [0, -1]])
        S = K * C
        A = -K
        I = Matrix([[1, 0], [0, 1]])
        J = Matrix([[0, -1], [1, 0]])

        assert K * K == -I, "K^2 should be -I"
        assert C * C == I, "C^2 should be I"
        assert K * C == -C * K, "DIII relation T C = -C T failed"
        assert S * S == I, "S = T C should square to I"
        assert A * A == -I, "Andreev involution should square to -I"
        assert A.T * A == I, "Andreev matrix should be isometric"
        assert A == J, "Andreev matrix convention mismatch"

        return True, "verified"
    except Exception as exc:  # pragma: no cover - defensive payload path
        return False, f"{type(exc).__name__}: {exc}"


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("--json", action="store_true", help="Emit JSON status payload")
    parser.add_argument("--out", default=None, help="Optional path for JSON output")
    args = parser.parse_args()

    is_verified, status = run_checks()

    payload = {
        "schema": "andreev_diii_kasparov_witness.v1",
        "is_verified": is_verified,
        "status": "verified" if is_verified else "failed",
        "message": status,
    }

    if args.json:
        if args.out is None:
            print(json.dumps(payload, indent=2, sort_keys=True))
        else:
            out = Path(args.out)
            out.parent.mkdir(parents=True, exist_ok=True)
            out.write_text(json.dumps(payload, indent=2, sort_keys=True), encoding="utf-8")
            print(f"wrote {out}")
        return

    if is_verified:
        print("Finite Andreev/DIII/Kasparov witness checks passed.")
        print("K =")
        print(Matrix([[0, 1], [-1, 0]]))
        print("C =")
        print(Matrix([[1, 0], [0, -1]]))
        print("S = T*C =")
        print(Matrix([[0, 1], [-1, 0]]) * Matrix([[1, 0], [0, -1]]))
        print("A = -K =")
        print(-Matrix([[0, 1], [-1, 0]]))
    else:
        print(f"Finite witness failed: {status}")


if __name__ == "__main__":
    main()
