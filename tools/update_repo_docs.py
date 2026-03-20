#!/usr/bin/env python3
from __future__ import annotations

import argparse
import subprocess
import sys
from dataclasses import dataclass
from pathlib import Path

if __package__ in (None, ""):
    sys.path.insert(0, str(Path(__file__).resolve().parent))
    from pathing import repo_root
else:
    from tools.pathing import repo_root


@dataclass(frozen=True)
class ExportSpec:
    module_name: str
    input_path: str
    output_path: str


DEFAULT_EXPORTS = [
    ExportSpec(
        module_name="KasparovCycle",
        input_path="lean/InfoGeometry/KK/KasparovCycle.lean",
        output_path="reports/dag/KasparovCycle.semantic-block.stdlib.json",
    ),
    ExportSpec(
        module_name="AnalyticalIndex",
        input_path="lean/InfoGeometry/Canonical/AnalyticalIndex.lean",
        output_path="reports/dag/AnalyticalIndex.semantic-block.stdlib.json",
    ),
    ExportSpec(
        module_name="OperatorAlgebraBridge",
        input_path="lean/InfoGeometry/Canonical/OperatorAlgebraBridge.lean",
        output_path="reports/dag/OperatorAlgebraBridge.semantic-block.stdlib.json",
    ),
    ExportSpec(
        module_name="GrandSynthesis",
        input_path="lean/InfoGeometry/Canonical/GrandSynthesis.lean",
        output_path="reports/dag/GrandSynthesis.semantic-block.stdlib.json",
    ),
]


def run(cmd: list[str], cwd: Path) -> None:
    print(f"[update-repo-docs] running: {' '.join(cmd)}", flush=True)
    subprocess.run(cmd, cwd=cwd, check=True)


def ensure_exists(path: Path) -> None:
    if not path.exists():
        raise SystemExit(f"missing required artifact: {path}")


def refresh_exports(root: Path, timeout: int) -> list[Path]:
    outputs: list[Path] = []
    for spec in DEFAULT_EXPORTS:
        out = root / spec.output_path
        run(
            [
                "python3",
                "tools/semantic_block_export.py",
                spec.input_path,
                spec.output_path,
                "--server-mode",
                "stdlib",
                "--inject-rpc-import",
                "--skip-wait-for-diagnostics",
                "--timeout",
                str(timeout),
            ],
            cwd=root,
        )
        outputs.append(out)
    return outputs


def current_export_paths(root: Path) -> list[Path]:
    outs = [root / spec.output_path for spec in DEFAULT_EXPORTS]
    for path in outs:
        ensure_exists(path)
    return outs


def run_skynet(root: Path, inputs: list[Path], seed: str, walk: str, top: int, json_out: str, md_out: str) -> None:
    cmd = ["python3", "tools/skynet_v2.py"]
    for path in inputs:
        cmd.extend(["--input", str(path)])
    cmd.extend(
        [
            "--seed",
            seed,
            "--walk",
            walk,
            "--top",
            str(top),
            "--json-out",
            json_out,
            "--md-out",
            md_out,
        ]
    )
    run(cmd, cwd=root)


def parse_args() -> argparse.Namespace:
    ap = argparse.ArgumentParser(
        description="Refresh tracked repository documentation from trusted semantic exports and Skynet v2 frontier packets."
    )
    ap.add_argument(
        "--seed",
        default="KasparovCycle.analyticalIndex",
        help="Seed used for frontier discovery.",
    )
    ap.add_argument(
        "--top",
        type=int,
        default=12,
        help="Frontier size for Skynet runs.",
    )
    ap.add_argument(
        "--refresh-exports",
        action="store_true",
        help="Regenerate the trusted semantic block exports before refreshing frontier/docs.",
    )
    ap.add_argument(
        "--export-timeout",
        type=int,
        default=900,
        help="Timeout used when refreshing trusted semantic block exports.",
    )
    ap.add_argument(
        "--skip-frontier",
        action="store_true",
        help="Do not rerun Skynet v2 frontier packets.",
    )
    ap.add_argument(
        "--skip-auto-docs",
        action="store_true",
        help="Do not regenerate docs/auto/index.md.",
    )
    return ap.parse_args()


def main() -> int:
    args = parse_args()
    root = repo_root()

    if args.refresh_exports:
        inputs = refresh_exports(root, args.export_timeout)
    else:
        inputs = current_export_paths(root)

    if not args.skip_frontier:
        run_skynet(
            root,
            inputs,
            seed=args.seed,
            walk="both",
            top=args.top,
            json_out="reports/dag/skynet-v2-frontier.json",
            md_out="reports/dag/skynet-v2-frontier.md",
        )
        run_skynet(
            root,
            inputs,
            seed=args.seed,
            walk="reverse",
            top=args.top,
            json_out="reports/dag/skynet-v2-frontier-reverse.json",
            md_out="reports/dag/skynet-v2-frontier-reverse.md",
        )

    if not args.skip_auto_docs:
        run(["python3", "tools/generate_auto_docs.py"], cwd=root)
        run(["python3", "tools/generate_self_optimization_report.py"], cwd=root)
        run(["python3", "tools/generate_surrogate_index.py"], cwd=root)
        run(["python3", "tools/generate_vacuity_index.py"], cwd=root)
        run(["python3", "tools/generate_bridge_thinness_index.py"], cwd=root)
        run(["python3", "tools/generate_llm_frontier_prompts.py"], cwd=root)

    print("[update-repo-docs] done", flush=True)
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
