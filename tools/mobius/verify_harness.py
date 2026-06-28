#!/usr/bin/env python3
from __future__ import annotations

import argparse
import csv
import json
import shutil
import subprocess
import tempfile
from dataclasses import asdict, dataclass
from pathlib import Path
from typing import Callable


ROOT = Path(__file__).resolve().parents[2]
DEFAULT_OUTPUT_DIR = ROOT / "tools" / "mobius" / "out"


@dataclass(frozen=True)
class Packet:
    name: str
    path: Path
    description: str
    matrix: dict[str, str]
    ring: str
    determinant: str
    trace: str
    sigma: str
    expected_classification: str
    fixed_points: list[str]
    projective_eigendirections: list[str]


@dataclass(frozen=True)
class EngineSpec:
    name: str
    marker: str | None
    supported_classes: tuple[str, ...]


@dataclass(frozen=True)
class EngineResult:
    status: str
    classification: str | None = None
    details: str = ""


ENGINE_SPECS: dict[str, EngineSpec] = {
    "sympy": EngineSpec("sympy", "MOBIUS_SYMPY_OK", ("hyperbolic", "parabolic", "elliptic", "loxodromic")),
    "gap": EngineSpec("gap", "MOBIUS_GAP_OK", ("hyperbolic", "parabolic", "elliptic", "loxodromic")),
    "lean": EngineSpec("lean", None, ("hyperbolic", "parabolic", "elliptic")),
    "sage": EngineSpec("sage", "MOBIUS_SAGE_OK", ("hyperbolic",)),
    "clifford": EngineSpec("clifford", "MOBIUS_CLIFFORD_OK", ("hyperbolic",)),
    "galgebra": EngineSpec("galgebra", "MOBIUS_GALGEBRA_OK", ("hyperbolic",)),
}


def default_packet_paths(root: Path = ROOT) -> list[Path]:
    return sorted((root / "tools" / "mobius").glob("mobius_packet_*.json"))


def load_packet(path: Path) -> Packet:
    payload = json.loads(path.read_text(encoding="utf-8"))
    expected = payload["expected"]
    return Packet(
        name=path.stem.removeprefix("mobius_packet_"),
        path=path,
        description=payload.get("description", ""),
        matrix=payload["matrix"],
        ring=payload["ring"],
        determinant=expected["determinant"],
        trace=expected["trace"],
        sigma=expected["sigma"],
        expected_classification=expected["classification"],
        fixed_points=list(expected.get("fixed_points", [])),
        projective_eigendirections=list(expected.get("projective_eigendirections", [])),
    )


def build_lean_driver(packet: Packet) -> str:
    class_name = packet.expected_classification
    return f"""import InfoGeometry.Canonical.MoebiusHurwitzDuality
import Mathlib.Data.Real.Basic
import Mathlib.Tactic

open InfoGeometry.MoebiusHurwitz

example : classifyMoebius ({packet.sigma} : ℝ) = MoebiusClassification.{class_name} := by
  norm_num [classifyMoebius]
"""


def _run_command(command: list[str], *, cwd: Path, input_text: str | None = None) -> tuple[int, str, str]:
    try:
        completed = subprocess.run(
            command,
            cwd=cwd,
            input=input_text,
            capture_output=True,
            text=True,
            timeout=180,
            check=False,
        )
        return completed.returncode, completed.stdout, completed.stderr
    except FileNotFoundError as exc:
        return 127, "", str(exc)
    except subprocess.TimeoutExpired as exc:
        stdout = exc.stdout.decode() if isinstance(exc.stdout, bytes) else (exc.stdout or "")
        stderr = exc.stderr.decode() if isinstance(exc.stderr, bytes) else (exc.stderr or "timeout")
        return 124, stdout, stderr


def _check_marker(spec: EngineSpec, code: int, stdout: str, stderr: str) -> EngineResult:
    if code != 0:
        return EngineResult("FAIL", details=(stderr or stdout or f"exit {code}").strip())
    if spec.marker and spec.marker not in stdout:
        return EngineResult("FAIL", details=f"missing marker {spec.marker}")
    return EngineResult("OK", details=stdout.strip())


def _gap_command(packet: Packet) -> list[str]:
    gap_bin = shutil.which("gap") or "/home/goutev/miniforge3/envs/sage/bin/gap"
    return [
        gap_bin,
        "-q",
        "-c",
        f'PacketName := "{packet.expected_classification}";; Read("tools/mobius/mobius_gap.g");',
    ]


def _sage_command(packet: Packet) -> list[str]:
    return ["/home/goutev/miniforge3/envs/sage/bin/python", "tools/sage/mobius_sage.py", packet.expected_classification]


def run_engine(spec: EngineSpec, packet: Packet, root: Path = ROOT) -> EngineResult:
    if packet.expected_classification not in spec.supported_classes:
        return EngineResult(
            "SKIP",
            classification=packet.expected_classification,
            details=f"{spec.name} supports only {', '.join(spec.supported_classes)}",
        )

    if spec.name == "sympy":
        code, out, err = _run_command(
            ["python3", "tools/mobius/mobius_sympy.py", packet.expected_classification],
            cwd=root,
        )
        return _check_marker(spec, code, out, err)

    if spec.name == "gap":
        code, out, err = _run_command(_gap_command(packet), cwd=root)
        return _check_marker(spec, code, out, err)

    if spec.name == "sage":
        code, out, err = _run_command(_sage_command(packet), cwd=root)
        return _check_marker(spec, code, out, err)

    if spec.name == "clifford":
        code, out, err = _run_command(["python3", "tools/mobius/mobius_clifford.py"], cwd=root)
        return _check_marker(spec, code, out, err)

    if spec.name == "galgebra":
        code, out, err = _run_command(["python3", "tools/mobius/mobius_galgebra.py"], cwd=root)
        return _check_marker(spec, code, out, err)

    if spec.name == "lean":
        with tempfile.TemporaryDirectory(prefix="mobius-lean-") as tmpdir:
            tmp_path = Path(tmpdir) / "PacketCheck.lean"
            tmp_path.write_text(build_lean_driver(packet), encoding="utf-8")
            code, out, err = _run_command([str(Path.home() / ".elan/bin/lake"), "env", "lean", str(tmp_path)], cwd=root)
            if code != 0:
                return EngineResult("FAIL", details=(stderr_or_stdout := (err or out or f"exit {code}")).strip())
            return EngineResult("OK", classification=packet.expected_classification, details=(out or "lean check passed").strip())

    return EngineResult("FAIL", details=f"unsupported engine {spec.name}")


Runner = Callable[[EngineSpec, Packet, Path], EngineResult]


def write_reports(rows: list[dict[str, str]], summary: dict[str, int], output_dir: Path) -> None:
    output_dir.mkdir(parents=True, exist_ok=True)
    json_path = output_dir / "verify_harness_summary.json"
    csv_path = output_dir / "verify_harness_summary.csv"

    json_path.write_text(json.dumps({"summary": summary, "rows": rows}, indent=2), encoding="utf-8")

    fieldnames = ["packet", "engine", "status", "classification", "details"]
    with csv_path.open("w", newline="", encoding="utf-8") as handle:
        writer = csv.DictWriter(handle, fieldnames=fieldnames)
        writer.writeheader()
        writer.writerows(rows)


def run_harness(
    *,
    packet_paths: list[Path],
    output_dir: Path,
    engine_names: list[str],
    root: Path = ROOT,
    runner: Runner = run_engine,
) -> dict[str, int]:
    rows: list[dict[str, str]] = []
    counts = {"passed": 0, "failed": 0, "skipped": 0, "total": 0}

    packets = [load_packet(path) for path in packet_paths]
    for packet in packets:
        for engine_name in engine_names:
            spec = ENGINE_SPECS[engine_name]
            result = runner(spec, packet, root)
            row = {
                "packet": packet.name,
                "engine": engine_name,
                "status": result.status,
                "classification": result.classification or packet.expected_classification,
                "details": result.details,
            }
            rows.append(row)
            counts["total"] += 1
            if result.status == "OK":
                counts["passed"] += 1
            elif result.status == "SKIP":
                counts["skipped"] += 1
            else:
                counts["failed"] += 1

    write_reports(rows, counts, output_dir)
    return counts


def parse_args() -> argparse.Namespace:
    parser = argparse.ArgumentParser(description="Cross-check Möbius packets across live repo engines.")
    parser.add_argument(
        "--packet",
        dest="packets",
        action="append",
        help="Path to a packet JSON file. Repeat for multiple packets. Defaults to built-in mobius_packet_*.json files.",
    )
    parser.add_argument(
        "--engine",
        dest="engines",
        action="append",
        choices=sorted(ENGINE_SPECS.keys()),
        help="Engine to run. Repeat for multiple engines. Defaults to all live engines.",
    )
    parser.add_argument(
        "--output-dir",
        type=Path,
        default=DEFAULT_OUTPUT_DIR,
        help=f"Directory for JSON/CSV summaries (default: {DEFAULT_OUTPUT_DIR}).",
    )
    return parser.parse_args()


def main() -> int:
    args = parse_args()
    packet_paths = [Path(p) for p in args.packets] if args.packets else default_packet_paths(ROOT)
    if not packet_paths:
        print("No packet files found.")
        return 1

    missing = [str(path) for path in packet_paths if not path.exists()]
    if missing:
        print("Missing packet files:")
        for path in missing:
            print(f"  - {path}")
        return 1

    engine_names = args.engines or list(ENGINE_SPECS.keys())
    summary = run_harness(packet_paths=packet_paths, output_dir=args.output_dir, engine_names=engine_names, root=ROOT)

    print(json.dumps(summary, indent=2, sort_keys=True))
    print(f"JSON summary: {(args.output_dir / 'verify_harness_summary.json')}" )
    print(f"CSV summary: {(args.output_dir / 'verify_harness_summary.csv')}" )
    return 0 if summary["failed"] == 0 else 1


if __name__ == "__main__":
    raise SystemExit(main())
