#!/usr/bin/env python3
"""Run Jixia over Lean files and build local tactic-training data.

Pipeline:

  Lean files
    -> Jixia raw JSON: declaration/symbol/elaboration/line
    -> jixia_trace_bridge.py normalized JSONL
    -> combined jixia_tactic_transitions.jsonl
    -> build_tactic_training_dataset.py SFT/DPO/failure JSONL

The script can also run in `--skip-jixia` mode to normalize pre-existing raw
Jixia JSON.  That mode is useful for tests and for resuming interrupted runs.
"""

from __future__ import annotations

import argparse
import json
import subprocess
import sys
from pathlib import Path
from typing import Any, Iterable

ROOT = Path(__file__).resolve().parents[2]
if str(ROOT) not in sys.path:
    sys.path.insert(0, str(ROOT))

from tools.infra.jixia_trace_bridge import run_bridge


SCHEMA = "info_geometry.jixia_batch_training.summary.v1"


LEAN_PATH_KEYS = {
    "file",
    "lean_file",
    "leanFile",
    "source_file",
    "sourceFile",
    "path",
    "source_path",
    "sourcePath",
}


def _looks_like_lean_path(value: str) -> bool:
    return value.endswith(".lean") and ("\n" not in value)


def _path_from_packet_string(value: str) -> Path | None:
    if not _looks_like_lean_path(value):
        return None
    path = Path(value)
    if path.is_absolute():
        return path
    return ROOT / path


def _collect_lean_paths_from_json(value: Any, *, key_hint: str | None = None) -> list[Path]:
    out: list[Path] = []
    if isinstance(value, dict):
        for key, item in value.items():
            out.extend(_collect_lean_paths_from_json(item, key_hint=str(key)))
    elif isinstance(value, list):
        for item in value:
            out.extend(_collect_lean_paths_from_json(item, key_hint=key_hint))
    elif isinstance(value, str):
        if key_hint in LEAN_PATH_KEYS or _looks_like_lean_path(value):
            path = _path_from_packet_string(value)
            if path is not None:
                out.append(path)
    return out


def lean_files_from_cone_packets(cone_packets: list[Path]) -> list[Path]:
    discovered: list[Path] = []
    for packet in cone_packets:
        data = json.loads(packet.read_text(encoding="utf-8"))
        discovered.extend(_collect_lean_paths_from_json(data))
    seen: set[str] = set()
    out: list[Path] = []
    for file in discovered:
        key = str(file)
        if key not in seen:
            seen.add(key)
            out.append(file)
    return out


def discover_lean_files(files: list[Path], prefixes: list[Path], cone_packets: list[Path] | None = None) -> list[Path]:
    discovered: list[Path] = []
    for file in files:
        if file.suffix == ".lean":
            discovered.append(file)
    if cone_packets:
        discovered.extend(lean_files_from_cone_packets(cone_packets))
    for prefix in prefixes:
        if prefix.is_file() and prefix.suffix == ".lean":
            discovered.append(prefix)
        elif prefix.is_dir():
            discovered.extend(sorted(prefix.rglob("*.lean")))
    seen: set[str] = set()
    out: list[Path] = []
    for file in discovered:
        key = str(file)
        if key not in seen:
            seen.add(key)
            out.append(file)
    return out


def raw_paths_for(raw_dir: Path, lean_file: Path) -> dict[str, Path]:
    rel = lean_file.with_suffix("")
    base = raw_dir / rel
    return {
        "dir": base,
        "declaration": base / "declaration.json",
        "symbol": base / "symbol.json",
        "elaboration": base / "elaboration.json",
        "line": base / "line.json",
    }


def normalized_dir_for(normalized_dir: Path, lean_file: Path) -> Path:
    return normalized_dir / lean_file.with_suffix("")


def run_jixia_file(*, lean_file: Path, jixia_bin: Path, raw_dir: Path, initializer: bool, extra_args: list[str]) -> dict[str, str | int]:
    paths = raw_paths_for(raw_dir, lean_file)
    paths["dir"].mkdir(parents=True, exist_ok=True)
    cmd = [
        "lake",
        "env",
        str(jixia_bin),
        "-d",
        str(paths["declaration"]),
        "-s",
        str(paths["symbol"]),
        "-e",
        str(paths["elaboration"]),
        "-l",
        str(paths["line"]),
    ]
    if initializer:
        cmd.append("-i")
    cmd.extend(extra_args)
    cmd.append(str(lean_file))
    completed = subprocess.run(cmd, text=True, capture_output=True, check=False)
    return {
        "file": str(lean_file),
        "returncode": completed.returncode,
        "stdout": completed.stdout,
        "stderr": completed.stderr,
    }


def normalize_file(*, lean_file: Path, raw_dir: Path, normalized_dir: Path) -> dict[str, object]:
    paths = raw_paths_for(raw_dir, lean_file)
    out_dir = normalized_dir_for(normalized_dir, lean_file)
    return run_bridge(
        declaration_json=paths["declaration"],
        symbol_json=paths["symbol"],
        elaboration_json=paths["elaboration"],
        line_json=paths["line"],
        output_dir=out_dir,
    )


def concat_jsonl(inputs: Iterable[Path], output: Path) -> int:
    output.parent.mkdir(parents=True, exist_ok=True)
    count = 0
    with output.open("w", encoding="utf-8") as out:
        for path in inputs:
            if not path.exists():
                continue
            with path.open("r", encoding="utf-8") as handle:
                for line in handle:
                    if not line.strip():
                        continue
                    out.write(line if line.endswith("\n") else line + "\n")
                    count += 1
    return count


def run_training_builder(*, combined_tactics: Path, dataset_dir: Path) -> dict[str, object]:
    dataset_dir.mkdir(parents=True, exist_ok=True)
    cmd = [
        sys.executable,
        str(ROOT / "tools/infra/build_tactic_training_dataset.py"),
        "--jixia-tactics",
        str(combined_tactics),
        "--out-sft",
        str(dataset_dir / "tactic_sft.jsonl"),
        "--out-dpo",
        str(dataset_dir / "tactic_dpo.jsonl"),
        "--out-failures",
        str(dataset_dir / "tactic_failures.jsonl"),
        "--stats-out",
        str(dataset_dir / "tactic_training_dataset.stats.json"),
    ]
    completed = subprocess.run(cmd, text=True, capture_output=True, check=False, cwd=ROOT)
    return {
        "returncode": completed.returncode,
        "stdout": completed.stdout,
        "stderr": completed.stderr,
        "dataset_dir": str(dataset_dir),
    }


def run_pipeline(args: argparse.Namespace) -> dict[str, object]:
    lean_files = discover_lean_files(args.file, args.prefix, args.cone_packet)
    if args.max_files is not None:
        lean_files = lean_files[: args.max_files]

    jixia_runs = []
    if not args.skip_jixia:
        for lean_file in lean_files:
            result = run_jixia_file(
                lean_file=lean_file,
                jixia_bin=args.jixia_bin,
                raw_dir=args.raw_dir,
                initializer=args.initializer,
                extra_args=args.jixia_arg,
            )
            jixia_runs.append(result)
            if result["returncode"] != 0 and not args.keep_going:
                break

    failed = [row for row in jixia_runs if row["returncode"] != 0]
    files_to_normalize = lean_files if args.skip_jixia or args.keep_going or not failed else lean_files[: len(jixia_runs)]

    normalized = []
    for lean_file in files_to_normalize:
        normalized.append(normalize_file(lean_file=lean_file, raw_dir=args.raw_dir, normalized_dir=args.normalized_dir))

    tactic_files = [
        normalized_dir_for(args.normalized_dir, lean_file) / "jixia_tactic_transitions.jsonl"
        for lean_file in files_to_normalize
    ]
    combined_tactics = args.combined_dir / "jixia_tactic_transitions.jsonl"
    combined_count = concat_jsonl(tactic_files, combined_tactics)

    training_result = None
    if args.build_training:
        training_result = run_training_builder(combined_tactics=combined_tactics, dataset_dir=args.dataset_dir)

    summary = {
        "schema": SCHEMA,
        "lean_files": [str(file) for file in lean_files],
        "cone_packets": [str(path) for path in args.cone_packet],
        "raw_dir": str(args.raw_dir),
        "normalized_dir": str(args.normalized_dir),
        "combined_tactics": str(combined_tactics),
        "combined_tactic_rows": combined_count,
        "skip_jixia": args.skip_jixia,
        "jixia_runs": jixia_runs,
        "normalized_files": len(normalized),
        "training_result": training_result,
    }
    args.summary_out.parent.mkdir(parents=True, exist_ok=True)
    args.summary_out.write_text(json.dumps(summary, indent=2, ensure_ascii=True, sort_keys=True) + "\n", encoding="utf-8")
    return summary


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--file", type=Path, action="append", default=[], help="Lean file to analyze; repeatable")
    parser.add_argument("--prefix", type=Path, action="append", default=[], help="Lean file or directory prefix; repeatable")
    parser.add_argument(
        "--cone-packet",
        type=Path,
        action="append",
        default=[],
        help="Causal cone packet JSON from arango_causal_chiral_cone_prompt.py; repeatable",
    )
    parser.add_argument("--max-files", type=int)
    parser.add_argument("--jixia-bin", type=Path, default=Path("external_refs/jixia/.lake/build/bin/jixia"))
    parser.add_argument("--raw-dir", type=Path, default=Path("artifacts/jixia/raw"))
    parser.add_argument("--normalized-dir", type=Path, default=Path("artifacts/jixia/normalized"))
    parser.add_argument("--combined-dir", type=Path, default=Path("artifacts/jixia/combined"))
    parser.add_argument("--dataset-dir", type=Path, default=Path("reports/training/jixia"))
    parser.add_argument("--summary-out", type=Path, default=Path("artifacts/jixia/jixia_batch_training_summary.json"))
    parser.add_argument("--skip-jixia", action="store_true", help="Normalize existing raw JSON without running Jixia")
    parser.add_argument("--initializer", action="store_true", default=True, help="Pass -i to Jixia")
    parser.add_argument("--no-initializer", action="store_false", dest="initializer")
    parser.add_argument("--jixia-arg", action="append", default=[], help="Extra raw argument passed to Jixia before the file")
    parser.add_argument("--keep-going", action="store_true")
    parser.add_argument("--build-training", action="store_true")
    args = parser.parse_args()

    if not args.file and not args.prefix and not args.cone_packet:
        parser.error("provide at least one --file, --prefix, or --cone-packet")

    summary = run_pipeline(args)
    print(json.dumps(summary, indent=2, ensure_ascii=True, sort_keys=True))
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
