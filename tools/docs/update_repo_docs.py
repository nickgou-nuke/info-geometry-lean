#!/usr/bin/env python3
from __future__ import annotations

import argparse
import json
import subprocess
import sys
from dataclasses import dataclass
from pathlib import Path

if __package__ in (None, ""):
    sys.path.insert(0, str(Path(__file__).resolve().parents[2]))
    from tools.pathing import repo_root
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


def normalize_repo_relative(root: Path, value: str) -> str | None:
    candidate = Path(value)
    if candidate.is_absolute():
        try:
            return str(candidate.resolve().relative_to(root))
        except ValueError:
            return None
    return str(candidate)


def export_spec_for_paths(root: Path, input_path: str, output_path: str) -> ExportSpec:
    rel_input = normalize_repo_relative(root, input_path)
    if rel_input is None:
        raise SystemExit(f"semantic export source is outside repo: {input_path}")
    return ExportSpec(
        module_name=Path(rel_input).stem,
        input_path=rel_input,
        output_path=output_path,
    )


def existing_export_specs(root: Path) -> list[ExportSpec]:
    dag_dir = root / "reports" / "dag"
    specs: list[ExportSpec] = []
    for path in sorted(dag_dir.glob("*.semantic-block.stdlib.json")):
        try:
            payload = json.loads(path.read_text(encoding="utf-8"))
        except Exception:
            continue
        source_file = str(payload.get("sourceFile", "")).strip()
        if not source_file or not source_file.endswith(".lean"):
            continue
        rel_input = normalize_repo_relative(root, source_file)
        if rel_input is None:
            continue
        specs.append(
            ExportSpec(
                module_name=Path(rel_input).stem,
                input_path=rel_input,
                output_path=str(path.relative_to(root)),
            )
        )
    return specs


def changed_tracked_lean_files(root: Path) -> list[str]:
    commands = [
        ["git", "show", "--name-only", "--pretty=format:", "HEAD"],
        ["git", "diff", "--name-only", "--relative"],
        ["git", "diff", "--cached", "--name-only", "--relative"],
    ]
    out: set[str] = set()
    for cmd in commands:
        try:
            raw = subprocess.check_output(cmd, cwd=root, text=True, stderr=subprocess.DEVNULL)
        except subprocess.CalledProcessError:
            continue
        for line in raw.splitlines():
            path = line.strip()
            if not path.startswith("lean/") or not path.endswith(".lean"):
                continue
            if not (root / path).exists():
                continue
            out.add(path)
    return sorted(out)


def changed_export_specs(root: Path) -> list[ExportSpec]:
    existing = {spec.input_path: spec for spec in existing_export_specs(root)}
    specs: list[ExportSpec] = []
    for input_path in changed_tracked_lean_files(root):
        spec = existing.get(input_path)
        if spec is None:
            spec = export_spec_for_paths(
                root,
                input_path=input_path,
                output_path=f"reports/dag/{Path(input_path).stem}.semantic-block.stdlib.json",
            )
        specs.append(spec)
    return specs


def refresh_exports(root: Path, timeout: int, mode: str) -> list[Path]:
    if mode == "default":
        specs = list(DEFAULT_EXPORTS)
    elif mode == "all":
        specs = existing_export_specs(root)
        if not specs:
            specs = list(DEFAULT_EXPORTS)
    elif mode == "changed":
        specs = changed_export_specs(root)
        if not specs:
            print("[update-repo-docs] no changed tracked Lean files; skipping export refresh", flush=True)
            return []
    else:
        raise SystemExit(f"unknown export refresh mode: {mode}")

    print(f"[update-repo-docs] refresh-exports mode `{mode}` modules={len(specs)}", flush=True)
    outputs: list[Path] = []
    failures: list[tuple[ExportSpec, bool]] = []
    for spec in specs:
        out = root / spec.output_path
        try:
            run(
                [
                    "python3",
                    "tools/frontier/semantic_block_export.py",
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
        except subprocess.CalledProcessError:
            stale = out.exists()
            failures.append((spec, stale))
            state = "keeping existing export" if stale else "no export available"
            print(
                f"[update-repo-docs] warning: export refresh failed for {spec.input_path} ({state})",
                flush=True,
            )
            continue
        outputs.append(out)

    if failures:
        kept = sum(1 for _, stale in failures if stale)
        missing = len(failures) - kept
        print(
            f"[update-repo-docs] export refresh completed with warnings: "
            f"{len(outputs)} succeeded, {len(failures)} failed, {kept} kept stale exports, {missing} missing",
            flush=True,
        )
    return outputs


def current_export_paths(root: Path) -> list[Path]:
    outs = sorted((root / "reports" / "dag").glob("*.semantic-block.stdlib.json"))
    if not outs:
        raise SystemExit("missing required artifact: reports/dag/*.semantic-block.stdlib.json")
    for path in outs:
        ensure_exists(path)
    return outs


def run_skynet(root: Path, inputs: list[Path], seed: str, walk: str, top: int, json_out: str, md_out: str) -> None:
    cmd = ["python3", "tools/frontier/skynet_v2.py"]
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
        nargs="?",
        const="default",
        choices=["default", "all", "changed"],
        help=(
            "Regenerate trusted semantic block exports before refreshing frontier/docs. "
            "Modes: `default` refreshes the tracked heavy-module subset, `all` refreshes every current semantic export, "
            "and `changed` refreshes tracked Lean files touched in HEAD or the current index/worktree."
        ),
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
    ap.add_argument(
        "--skip-decl-refresh",
        action="store_true",
        help="Do not refresh the public declaration-DAG artifacts before causal-order reports.",
    )
    return ap.parse_args()


def main() -> int:
    args = parse_args()
    root = repo_root()

    if args.refresh_exports:
        refresh_exports(root, args.export_timeout, args.refresh_exports)
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
        run(["python3", "tools/docs/generate_auto_docs.py"], cwd=root)
        run(["python3", "tools/generate_self_optimization_report.py"], cwd=root)
        run(["python3", "tools/generate_surrogate_index.py"], cwd=root)
        run(["python3", "tools/generate_vacuity_index.py"], cwd=root)
        run(["python3", "tools/generate_bridge_thinness_index.py"], cwd=root)
        if not args.skip_decl_refresh:
            run(["python3", "tools/infra/refresh_decl_graph.py"], cwd=root)
        run(
            [
                "python3",
                "tools/infra/generate_causal_report.py",
                "--allow-partial-coverage",
                "--out",
                "reports/dag/true-root-order.md",
                "--json-out",
                "reports/dag/true-root-order.json",
            ],
            cwd=root,
        )
        run(["python3", "tools/infra/classify_missing_all.py"], cwd=root)
        run(["python3", "tools/infra/generate_theorem_surface_index.py"], cwd=root)
        run(["python3", "tools/infra/plot_decl_graph.py"], cwd=root)
        run(["python3", "tools/infra/generate_source_sink_compression.py"], cwd=root)
        run(["python3", "tools/infra/select_openclaw_target.py"], cwd=root)
        run(["python3", "tools/generate_unification_index.py"], cwd=root)
        run(["python3", "tools/generate_debt_candidates.py"], cwd=root)
        run(["python3", "tools/generate_bridge_candidates.py"], cwd=root)
        run(["python3", "tools/generate_llm_frontier_prompts.py"], cwd=root)
        run(["python3", "tools/generate_llm_debt_prompts.py"], cwd=root)

    print("[update-repo-docs] done", flush=True)
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
