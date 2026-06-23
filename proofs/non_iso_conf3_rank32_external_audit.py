#!/usr/bin/env python3
r"""External Rank-32 audit for C^8 \ V(q(a)q(b)q(a-b)).

This script runs the heavy Macaulay2 Oaku/Dlocalize workflow (via
`compute_derham.m2`) and emits a compact JSON certificate intended for Lean
ingestion by `lean/InfoGeometry/Projective/NonIsoConf3RankIngestion.lean`.

On timeout/resource exhaustion it records a certified-failure payload so Lean can
safely distinguish "trusted numeric certificate" from "computational status".
"""

from __future__ import annotations

import argparse
import json
import re
import shutil
import subprocess
import sys
from dataclasses import dataclass
from datetime import datetime, timezone
from pathlib import Path
from typing import Any


@dataclass
class AuditResult:
    dim_ambient: int
    betti_numbers: list[int]
    total_rank: int
    is_verified: bool
    status: str
    engine: str
    source: str
    message: str | None = None


def now_iso() -> str:
    return datetime.now(timezone.utc).replace(microsecond=0).isoformat()


def process_text(data: str | bytes | None) -> str:
    """Normalize subprocess output to text.

    `subprocess.TimeoutExpired` can carry `stdout` as bytes even when
    `subprocess.run(..., text=True)` was used.
    """
    if data is None:
        return ""
    if isinstance(data, bytes):
        return data.decode(errors="replace")
    return data


def run_cmd(cmd: list[str], timeout: int | None) -> tuple[int, str, str, bool]:
    """Run a subprocess and return (rc, out, err, timed_out)."""
    try:
        cp = subprocess.run(
            cmd,
            stdout=subprocess.PIPE,
            stderr=subprocess.STDOUT,
            text=True,
            timeout=timeout,
            check=False,
        )
        return cp.returncode, cp.stdout, "", False
    except subprocess.TimeoutExpired as exc:
        output = process_text(exc.stdout)
        error = process_text(exc.stderr) or "timeout"
        return 124, output, error, True
    except FileNotFoundError:
        return 127, "", "binary-not-found", False


def parse_list(line: str) -> list[int] | None:
    # Parse a bracketed comma/space separated list of nonnegative integers.
    # Example: [1, 2, 1, 0]
    m = re.search(r"\[[^\]]*\]", line)
    if not m:
        return None
    body = m.group(0).strip("[]")
    if not body.strip():
        return []
    nums: list[int] = []
    for tok in re.split(r"[\s,]+", body.strip()):
        if not tok:
            continue
        if not re.fullmatch(r"-?\d+", tok):
            return None
        v = int(tok)
        if v < 0:
            return None
        nums.append(v)
    return nums


def parse_macaulay2_rank_table(text: str) -> list[int] | None:
    """Parse Macaulay2 tables of the form `{0 => QQ^1, 1 => QQ^3}`.

    Macaulay2 prints a one-dimensional vector space as `QQ` or `QQ^1`.
    Missing degrees are filled with `0`.
    """
    matches = re.findall(r"(\d+)\s*=>\s*QQ(?:\^(\d+))?", text)
    if not matches:
        return None
    degree_to_rank: dict[int, int] = {}
    for degree_raw, rank_raw in matches:
        degree = int(degree_raw)
        rank = int(rank_raw) if rank_raw else 1
        degree_to_rank[degree] = rank
    max_degree = max(degree_to_rank)
    return [degree_to_rank.get(i, 0) for i in range(max_degree + 1)]


def parse_output(output: str) -> tuple[list[int] | None, str]:
    marker = "DLOCALIZE_EXT:result="
    if marker in output:
        tail = output.split(marker, 1)[1]
        parsed = parse_list(tail)
        if parsed is not None:
            return parsed, "ok"
        parsed = parse_macaulay2_rank_table(tail)
        if parsed is not None:
            return parsed, "ok"
        return None, "marker-found-no-list-or-rank-table"
    marker = "MACAULAY2:dlocalize_ext_table="
    if marker in output:
        tail = output.split(marker, 1)[1]
        parsed = parse_macaulay2_rank_table(tail)
        if parsed is not None:
            return parsed, "ok"
        return None, "macaulay2-marker-found-no-rank-table"
    if "timed out" in output.lower():
        return None, "timeout"
    return None, "marker-missing"


def run_macaulay2(
    timeout: int,
    m2_path: str,
    script_path: Path,
    log_path: Path | None,
    dim_ambient: int,
) -> AuditResult:
    cmd = [m2_path, "--script", str(script_path)]
    rc, out, err, did_timeout = run_cmd(cmd, timeout)

    if log_path is not None:
        log_path.parent.mkdir(parents=True, exist_ok=True)
        log_path.write_text(out, encoding="utf-8")

    betti: list[int] | None
    status: str
    is_verified = False

    if did_timeout:
        betti = None
        status = "timeout"
        message = f"m2-timeout (limit={timeout}s)"
    elif rc != 0:
        betti = None
        status = "execution-failed"
        message = f"exit={rc}, err={err}"
    else:
        betti, parse_status = parse_output(out)
        status = "verified" if betti is not None else "parse-failed"
        is_verified = betti is not None
        message = None if is_verified else parse_status

    if is_verified and betti is not None:
        total = sum(betti)
        return AuditResult(
            dim_ambient=dim_ambient,
            betti_numbers=betti,
            total_rank=total,
            is_verified=True,
            status=status,
            engine="Macaulay2/BernsteinSato",
            source=str(script_path),
            message=message,
        )

    return AuditResult(
        dim_ambient=dim_ambient,
        betti_numbers=[],
        total_rank=0,
        is_verified=False,
        status=status,
        engine="Macaulay2/BernsteinSato",
        source=str(script_path),
        message=message,
    )


def write_certificate(path: Path, payload: dict[str, Any]) -> None:
    path.parent.mkdir(parents=True, exist_ok=True)
    with path.open("w", encoding="utf-8") as f:
        json.dump(payload, f, indent=2, sort_keys=True)


def main() -> int:
    parser = argparse.ArgumentParser()
    parser.add_argument(
        "--script",
        default="compute_derham.m2",
        help="Path to Macaulay2 D-module audit script.",
    )
    parser.add_argument(
        "--m2-timeout",
        type=int,
        default=900,
        help="Macaulay2 wall-clock timeout in seconds.",
    )
    parser.add_argument(
        "--output",
        default="artifacts/non_iso_conf3_rank32_audit.json",
        help="Where to write certificate JSON.",
    )
    parser.add_argument(
        "--dim-ambient",
        type=int,
        default=8,
        help="Ambient complex dimension of the audited complement.",
    )
    parser.add_argument(
        "--log",
        default=None,
        help="Optional path to write raw backend log text.",
    )
    args = parser.parse_args()

    m2_path = shutil.which("M2") or shutil.which("m2-stack")
    if m2_path is None:
        payload: dict[str, Any] = {
            "schema": "non_iso_conf3_rank32_external_audit.v1",
            "generatedAt": now_iso(),
            "dim_ambient": args.dim_ambient,
            "betti_numbers": [],
            "total_rank": 0,
            "is_verified": False,
            "status": "missing-backend",
            "engine": "Macaulay2/BernsteinSato",
            "message": "M2 binary not found in PATH",
        }
        write_certificate(Path(args.output), payload)
        print(f"[non_iso_conf3_rank32_external_audit] missing M2 (wrote {args.output})")
        return 1

    log_path = Path(args.log) if args.log else None
    result = run_macaulay2(args.m2_timeout, m2_path, Path(args.script), log_path, args.dim_ambient)

    payload = {
        "schema": "non_iso_conf3_rank32_external_audit.v1",
        "generatedAt": now_iso(),
        "dim_ambient": result.dim_ambient,
        "betti_numbers": result.betti_numbers,
        "total_rank": result.total_rank,
        "is_verified": result.is_verified,
        "status": result.status,
        "engine": result.engine,
        "source": result.source,
    }
    if result.message:
        payload["message"] = result.message

    write_certificate(Path(args.output), payload)

    if result.is_verified:
        print(f"[non_iso_conf3_rank32_external_audit] verified: total_rank={result.total_rank} -> {args.output}")
        return 0

    print(f"[non_iso_conf3_rank32_external_audit] not verified: status={result.status}")
    print(f"  message={result.message}")
    return 1


if __name__ == "__main__":
    sys.exit(main())
