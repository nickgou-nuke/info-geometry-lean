#!/usr/bin/env python3
from __future__ import annotations

import argparse
import json
import subprocess
import sys
import time
from dataclasses import asdict, dataclass
from datetime import datetime, timezone
from pathlib import Path
from typing import Any


REPO_ROOT = Path(__file__).resolve().parents[2]

DEFAULT_LOCKED_MODULES = [
    "InfoGeometry.Canonical.ProjectorEquivariance",
    "InfoGeometry.Dynamics.UnruhKMS",
    "InfoGeometry.Canonical.ModularSuperchargeClosure",
]

PROFILE_PRESETS: dict[str, dict[str, Any]] = {
    "hermes-hybrid": {
        "dim": 262144,
        "epochs": 6,
        "learning_rate": 0.05,
        "radius": 2,
        "candidate_limit": 2500,
        "top_k": 100,
    },
    "dgx-spark": {
        "dim": 524288,
        "epochs": 8,
        "learning_rate": 0.04,
        "radius": 2,
        "candidate_limit": 5000,
        "top_k": 200,
    },
}


@dataclass
class StepResult:
    step: str
    status: str
    command: list[str]
    start_utc: str
    end_utc: str
    duration_sec: float
    returncode: int
    stdout_log: str
    stderr_log: str


def _utc_now() -> str:
    return datetime.now(timezone.utc).isoformat()


def _utc_stamp() -> str:
    return datetime.now(timezone.utc).strftime("%Y%m%dT%H%M%SZ")


def _resolve_profile_value(
    profile: str,
    explicit: int | float | None,
    key: str,
) -> int | float:
    if explicit is not None:
        return explicit
    return PROFILE_PRESETS[profile][key]


def _write_text(path: Path, text: str) -> None:
    path.parent.mkdir(parents=True, exist_ok=True)
    path.write_text(text, encoding="utf-8")


def _run_step(
    *,
    step: str,
    command: list[str],
    logs_dir: Path,
    dry_run: bool,
) -> StepResult:
    start = _utc_now()
    t0 = time.perf_counter()
    stdout_log = logs_dir / f"{step}.stdout.log"
    stderr_log = logs_dir / f"{step}.stderr.log"

    if dry_run:
        _write_text(stdout_log, "[dry-run]\n" + " ".join(command) + "\n")
        _write_text(stderr_log, "")
        end = _utc_now()
        return StepResult(
            step=step,
            status="dry_run",
            command=command,
            start_utc=start,
            end_utc=end,
            duration_sec=round(time.perf_counter() - t0, 6),
            returncode=0,
            stdout_log=str(stdout_log),
            stderr_log=str(stderr_log),
        )

    proc = subprocess.run(command, cwd=REPO_ROOT, text=True, capture_output=True, check=False)
    _write_text(stdout_log, proc.stdout or "")
    _write_text(stderr_log, proc.stderr or "")
    end = _utc_now()
    return StepResult(
        step=step,
        status="ok" if proc.returncode == 0 else "failed",
        command=command,
        start_utc=start,
        end_utc=end,
        duration_sec=round(time.perf_counter() - t0, 6),
        returncode=int(proc.returncode),
        stdout_log=str(stdout_log),
        stderr_log=str(stderr_log),
    )


def parse_args() -> argparse.Namespace:
    ap = argparse.ArgumentParser(
        description=(
            "Hybrid DGX Spark orchestrator: deterministic local lane for "
            "ATS dataset build -> link-scorer train -> Arango rerank -> "
            "optional dual-hypothesis sampler/fuser gate, with optional locked Lean gate."
        )
    )
    ap.add_argument("--profile", choices=sorted(PROFILE_PRESETS.keys()), default="hermes-hybrid")
    ap.add_argument("--center", default="", help="Center declaration used by rerank step.")
    ap.add_argument("--out-dir", default="reports/training/dgx_hybrid")
    ap.add_argument("--run-id", default="")
    ap.add_argument("--manifest-out", default="")
    ap.add_argument("--dry-run", action="store_true")

    ap.add_argument("--skip-locked-build", action="store_true")
    ap.add_argument("--skip-dataset", action="store_true")
    ap.add_argument("--skip-train", action="store_true")
    ap.add_argument("--skip-rerank", action="store_true")
    ap.add_argument("--with-hypothesis-loop", action="store_true")
    ap.add_argument("--skip-hypothesis-sampler", action="store_true")
    ap.add_argument("--skip-hypothesis-fuser", action="store_true")
    ap.add_argument("--locked-module", action="append", default=[])

    ap.add_argument("--dataset-out", default="")
    ap.add_argument("--dataset-stats-out", default="")
    ap.add_argument("--model-out", default="")
    ap.add_argument("--metrics-out", default="")
    ap.add_argument("--rerank-out", default="")
    ap.add_argument("--rerank-rows-out", default="")

    ap.add_argument("--dim", type=int, default=None)
    ap.add_argument("--epochs", type=int, default=None)
    ap.add_argument("--learning-rate", type=float, default=None)
    ap.add_argument("--radius", type=int, default=None)
    ap.add_argument("--candidate-limit", type=int, default=None)
    ap.add_argument("--top-k", type=int, default=None)
    ap.add_argument("--decl-kind-filter", default="theorem,lemma,axiom")

    ap.add_argument("--mode", choices=["local", "arango-http"], default="local")
    ap.add_argument("--arango-input", default="artifacts/leantrail/arango")
    ap.add_argument("--arango-input-format", choices=["snapshot", "arango-json"], default="arango-json")
    ap.add_argument("--arango-endpoint", default="http://127.0.0.1:8529")
    ap.add_argument("--arango-database", default="infogeometry")
    ap.add_argument("--arango-username", default="root")
    ap.add_argument("--arango-password", default="")
    ap.add_argument("--arango-nodes-collection", default="ig_nodes")
    ap.add_argument("--arango-edges-collection", default="ig_edges")
    ap.set_defaults(declaration_only=True)
    ap.add_argument("--declaration-only", dest="declaration_only", action="store_true")
    ap.add_argument("--include-non-declarations", dest="declaration_only", action="store_false")

    ap.add_argument("--hyp-goal", default="")
    ap.add_argument("--hyp-goal-file", default="")
    ap.add_argument("--hyp-dag-context", default="")
    ap.add_argument("--hyp-context-file", action="append", default=[])
    ap.add_argument("--hyp-candidates-out", default="")
    ap.add_argument("--hyp-sampler-manifest-out", default="")
    ap.add_argument("--hyp-input-candidates", default="")
    ap.add_argument("--hyp-fused-out", default="")
    ap.add_argument("--hyp-fused-rows-out", default="")
    ap.add_argument("--hyp-gate-dir", default="")
    ap.add_argument("--hyp-model-base", default="qwen3-proposer")
    ap.add_argument("--hyp-model-tuned", default="deepseek-formalizer")
    ap.add_argument("--hyp-base-url-base", default="http://127.0.0.1:8000/v1")
    ap.add_argument("--hyp-base-url-tuned", default="http://127.0.0.1:8001/v1")
    ap.add_argument("--hyp-api-key-base", default="EMPTY")
    ap.add_argument("--hyp-api-key-tuned", default="EMPTY")
    ap.add_argument("--hyp-provider-base", choices=["openai-chat", "gemini-cli"], default="openai-chat")
    ap.add_argument("--hyp-provider-tuned", choices=["openai-chat", "gemini-cli"], default="openai-chat")
    ap.add_argument("--hyp-gemini-bin-base", default="gemini")
    ap.add_argument("--hyp-gemini-bin-tuned", default="gemini")
    ap.add_argument("--hyp-gemini-arg-base", action="append", default=[])
    ap.add_argument("--hyp-gemini-arg-tuned", action="append", default=[])
    ap.add_argument("--hyp-gemini-input-mode-base", choices=["stdin", "arg"], default="stdin")
    ap.add_argument("--hyp-gemini-input-mode-tuned", choices=["stdin", "arg"], default="stdin")
    ap.add_argument("--hyp-gemini-prompt-flag-base", default="-p")
    ap.add_argument("--hyp-gemini-prompt-flag-tuned", default="-p")
    ap.add_argument("--hyp-samples-base", type=int, default=4)
    ap.add_argument("--hyp-samples-tuned", type=int, default=4)
    ap.add_argument("--hyp-temperature-base", type=float, default=0.95)
    ap.add_argument("--hyp-temperature-tuned", type=float, default=0.55)
    ap.add_argument("--hyp-top-k", type=int, default=8)
    ap.add_argument("--hyp-max-pass", type=int, default=2)
    ap.add_argument("--hyp-compile-timeout-sec", type=int, default=120)
    ap.add_argument("--hyp-emit-skills", action="store_true")
    ap.add_argument("--hyp-strict-check", action="store_true")
    ap.add_argument("--hyp-skip-lean-gate", action="store_true")
    return ap.parse_args()


def _python() -> str:
    return sys.executable or "python3"


def main() -> int:
    args = parse_args()
    run_id = args.run_id.strip() or _utc_stamp()
    out_dir = Path(args.out_dir).resolve()
    logs_dir = out_dir / "logs" / run_id
    logs_dir.mkdir(parents=True, exist_ok=True)

    dataset_out = Path(args.dataset_out).resolve() if args.dataset_out else out_dir / f"{run_id}.link_ats_dataset.jsonl"
    dataset_stats_out = (
        Path(args.dataset_stats_out).resolve() if args.dataset_stats_out else out_dir / f"{run_id}.link_ats_dataset.stats.json"
    )
    model_out = Path(args.model_out).resolve() if args.model_out else out_dir / f"{run_id}.link_scorer_model.npz"
    metrics_out = Path(args.metrics_out).resolve() if args.metrics_out else out_dir / f"{run_id}.link_scorer_metrics.json"
    rerank_out = Path(args.rerank_out).resolve() if args.rerank_out else out_dir / f"{run_id}.arango_link_rerank.json"
    rerank_rows_out = (
        Path(args.rerank_rows_out).resolve() if args.rerank_rows_out else out_dir / f"{run_id}.arango_link_rerank.rows.jsonl"
    )
    hyp_candidates_out = (
        Path(args.hyp_candidates_out).resolve()
        if args.hyp_candidates_out
        else out_dir / f"{run_id}.hypothesis_candidates.jsonl"
    )
    hyp_sampler_manifest_out = (
        Path(args.hyp_sampler_manifest_out).resolve()
        if args.hyp_sampler_manifest_out
        else out_dir / f"{run_id}.hypothesis_sampler.manifest.json"
    )
    hyp_fused_out = (
        Path(args.hyp_fused_out).resolve()
        if args.hyp_fused_out
        else out_dir / f"{run_id}.hypothesis_fused_gated.json"
    )
    hyp_fused_rows_out = (
        Path(args.hyp_fused_rows_out).resolve()
        if args.hyp_fused_rows_out
        else out_dir / f"{run_id}.hypothesis_fused_gated.rows.jsonl"
    )
    manifest_out = Path(args.manifest_out).resolve() if args.manifest_out else out_dir / f"{run_id}.manifest.json"

    dim = int(_resolve_profile_value(args.profile, args.dim, "dim"))
    epochs = int(_resolve_profile_value(args.profile, args.epochs, "epochs"))
    learning_rate = float(_resolve_profile_value(args.profile, args.learning_rate, "learning_rate"))
    radius = int(_resolve_profile_value(args.profile, args.radius, "radius"))
    candidate_limit = int(_resolve_profile_value(args.profile, args.candidate_limit, "candidate_limit"))
    top_k = int(_resolve_profile_value(args.profile, args.top_k, "top_k"))

    if not args.skip_rerank and not args.center.strip():
        raise SystemExit("--center is required unless --skip-rerank is set")
    if dim <= 0 or epochs <= 0 or radius < 0 or candidate_limit <= 0 or top_k <= 0:
        raise SystemExit("invalid numeric settings")
    if args.with_hypothesis_loop:
        if args.hyp_top_k <= 0 or args.hyp_max_pass <= 0:
            raise SystemExit("invalid hypothesis settings: --hyp-top-k and --hyp-max-pass must be > 0")
        if args.hyp_samples_base < 0 or args.hyp_samples_tuned < 0:
            raise SystemExit("invalid hypothesis settings: sample counts must be >= 0")

    modules = [m.strip() for m in args.locked_module if m.strip()] or list(DEFAULT_LOCKED_MODULES)
    py = _python()
    steps: list[StepResult] = []

    if not args.skip_locked_build:
        cmd = [py, str(REPO_ROOT / "tools/infra/run_locked_lake_build.py"), "--wait-for-build-lock", *modules]
        result = _run_step(step="locked_build", command=cmd, logs_dir=logs_dir, dry_run=args.dry_run)
        steps.append(result)
        if result.returncode != 0:
            _finalize_manifest(
                manifest_out=manifest_out,
                run_id=run_id,
                args=args,
                steps=steps,
                status="failed",
                artifacts={},
            )
            return result.returncode

    if not args.skip_dataset:
        cmd = [
            py,
            str(REPO_ROOT / "tools/infra/build_link_ats_dataset.py"),
            "--out",
            str(dataset_out),
            "--stats-out",
            str(dataset_stats_out),
        ]
        result = _run_step(step="build_dataset", command=cmd, logs_dir=logs_dir, dry_run=args.dry_run)
        steps.append(result)
        if result.returncode != 0:
            _finalize_manifest(
                manifest_out=manifest_out,
                run_id=run_id,
                args=args,
                steps=steps,
                status="failed",
                artifacts={},
            )
            return result.returncode

    if not args.skip_train:
        cmd = [
            py,
            str(REPO_ROOT / "tools/infra/train_link_scorer.py"),
            "--dataset",
            str(dataset_out),
            "--model-out",
            str(model_out),
            "--metrics-out",
            str(metrics_out),
            "--dim",
            str(dim),
            "--epochs",
            str(epochs),
            "--learning-rate",
            str(learning_rate),
        ]
        result = _run_step(step="train_link_scorer", command=cmd, logs_dir=logs_dir, dry_run=args.dry_run)
        steps.append(result)
        if result.returncode != 0:
            _finalize_manifest(
                manifest_out=manifest_out,
                run_id=run_id,
                args=args,
                steps=steps,
                status="failed",
                artifacts={},
            )
            return result.returncode

    if not args.skip_rerank:
        cmd = [
            py,
            str(REPO_ROOT / "tools/infra/rerank_arango_links.py"),
            "--mode",
            args.mode,
            "--center",
            args.center.strip(),
            "--radius",
            str(radius),
            "--candidate-limit",
            str(candidate_limit),
            "--top-k",
            str(top_k),
            "--model",
            str(model_out),
            "--out",
            str(rerank_out),
            "--rows-out",
            str(rerank_rows_out),
            "--decl-kind-filter",
            args.decl_kind_filter,
        ]
        if args.declaration_only:
            cmd.append("--declaration-only")
        else:
            cmd.append("--include-non-declarations")

        if args.mode == "local":
            cmd.extend(
                [
                    "--input",
                    str(Path(args.arango_input).resolve()),
                    "--input-format",
                    args.arango_input_format,
                ]
            )
        else:
            cmd.extend(
                [
                    "--endpoint",
                    args.arango_endpoint,
                    "--database",
                    args.arango_database,
                    "--username",
                    args.arango_username,
                    "--password",
                    args.arango_password,
                    "--nodes-collection",
                    args.arango_nodes_collection,
                    "--edges-collection",
                    args.arango_edges_collection,
                ]
            )

        result = _run_step(step="rerank_arango_links", command=cmd, logs_dir=logs_dir, dry_run=args.dry_run)
        steps.append(result)
        if result.returncode != 0:
            _finalize_manifest(
                manifest_out=manifest_out,
                run_id=run_id,
                args=args,
                steps=steps,
                status="failed",
                artifacts={},
            )
            return result.returncode

    if args.with_hypothesis_loop:
        hyp_goal = str(args.hyp_goal).strip()
        if not hyp_goal and not str(args.hyp_goal_file).strip() and args.center.strip():
            hyp_goal = args.center.strip()
        if not hyp_goal and not str(args.hyp_goal_file).strip():
            raise SystemExit(
                "--with-hypothesis-loop requires --hyp-goal or --hyp-goal-file "
                "(or provide --center so it can be used as fallback goal)."
            )

        hyp_candidates_input = (
            Path(args.hyp_input_candidates).resolve() if args.hyp_input_candidates else hyp_candidates_out
        )

        if not args.skip_hypothesis_sampler:
            cmd = [
                py,
                str(REPO_ROOT / "tools/infra/dual_hypothesis_sampler.py"),
            ]
            if args.hyp_goal_file:
                cmd.extend(["--goal-file", str(Path(args.hyp_goal_file).resolve())])
            else:
                cmd.extend(["--goal", hyp_goal])
            for ctx_path in args.hyp_context_file:
                cmd.extend(["--context-file", str(Path(ctx_path).resolve())])
            if args.hyp_dag_context:
                cmd.extend(["--dag-context", str(Path(args.hyp_dag_context).resolve())])
            elif not args.skip_rerank:
                cmd.extend(["--dag-context", str(rerank_out)])
            cmd.extend(
                [
                    "--base-url-base",
                    args.hyp_base_url_base,
                    "--model-base",
                    args.hyp_model_base,
                    "--api-key-base",
                    args.hyp_api_key_base,
                    "--provider-base",
                    args.hyp_provider_base,
                    "--gemini-bin-base",
                    args.hyp_gemini_bin_base,
                    "--gemini-input-mode-base",
                    args.hyp_gemini_input_mode_base,
                    "--gemini-prompt-flag-base",
                    args.hyp_gemini_prompt_flag_base,
                    "--samples-base",
                    str(args.hyp_samples_base),
                    "--temperature-base",
                    str(args.hyp_temperature_base),
                    "--base-url-tuned",
                    args.hyp_base_url_tuned,
                    "--model-tuned",
                    args.hyp_model_tuned,
                    "--api-key-tuned",
                    args.hyp_api_key_tuned,
                    "--provider-tuned",
                    args.hyp_provider_tuned,
                    "--gemini-bin-tuned",
                    args.hyp_gemini_bin_tuned,
                    "--gemini-input-mode-tuned",
                    args.hyp_gemini_input_mode_tuned,
                    "--gemini-prompt-flag-tuned",
                    args.hyp_gemini_prompt_flag_tuned,
                    "--samples-tuned",
                    str(args.hyp_samples_tuned),
                    "--temperature-tuned",
                    str(args.hyp_temperature_tuned),
                    "--out",
                    str(hyp_candidates_out),
                    "--manifest-out",
                    str(hyp_sampler_manifest_out),
                ]
            )
            for gem_arg in args.hyp_gemini_arg_base:
                cmd.extend(["--gemini-arg-base", str(gem_arg)])
            for gem_arg in args.hyp_gemini_arg_tuned:
                cmd.extend(["--gemini-arg-tuned", str(gem_arg)])
            if args.dry_run:
                cmd.append("--dry-run")
            result = _run_step(step="hypothesis_sampler", command=cmd, logs_dir=logs_dir, dry_run=args.dry_run)
            steps.append(result)
            if result.returncode != 0:
                _finalize_manifest(
                    manifest_out=manifest_out,
                    run_id=run_id,
                    args=args,
                    steps=steps,
                    status="failed",
                    artifacts={},
                )
                return result.returncode
            hyp_candidates_input = hyp_candidates_out
        elif not args.dry_run and not hyp_candidates_input.exists():
            raise SystemExit(
                "--skip-hypothesis-sampler was set but hypothesis input is missing: "
                f"{hyp_candidates_input}"
            )

        if not args.skip_hypothesis_fuser:
            cmd = [
                py,
                str(REPO_ROOT / "tools/infra/hypothesis_fuser_and_lean_gate.py"),
                "--input",
                str(hyp_candidates_input),
                "--top-k",
                str(args.hyp_top_k),
                "--max-pass",
                str(args.hyp_max_pass),
                "--compile-timeout-sec",
                str(args.hyp_compile_timeout_sec),
                "--out",
                str(hyp_fused_out),
                "--rows-out",
                str(hyp_fused_rows_out),
            ]
            if args.hyp_goal_file:
                cmd.extend(["--goal-file", str(Path(args.hyp_goal_file).resolve())])
            else:
                cmd.extend(["--goal", hyp_goal])
            if args.hyp_gate_dir:
                cmd.extend(["--gate-dir", str(Path(args.hyp_gate_dir).resolve())])
            if args.hyp_skip_lean_gate:
                cmd.append("--skip-lean-gate")
            if args.hyp_emit_skills:
                cmd.append("--emit-skills")
            if args.hyp_strict_check:
                cmd.append("--strict-check")

            result = _run_step(step="hypothesis_fuser_gate", command=cmd, logs_dir=logs_dir, dry_run=args.dry_run)
            steps.append(result)
            if result.returncode != 0:
                _finalize_manifest(
                    manifest_out=manifest_out,
                    run_id=run_id,
                    args=args,
                    steps=steps,
                    status="failed",
                    artifacts={},
                )
                return result.returncode

    artifacts = {
        "dataset": str(dataset_out),
        "dataset_stats": str(dataset_stats_out),
        "model": str(model_out),
        "metrics": str(metrics_out),
        "rerank_report": str(rerank_out),
        "rerank_rows": str(rerank_rows_out),
        "logs_dir": str(logs_dir),
    }
    if args.with_hypothesis_loop:
        artifacts["hypothesis_candidates"] = (
            str(Path(args.hyp_input_candidates).resolve()) if args.hyp_input_candidates else str(hyp_candidates_out)
        )
        artifacts["hypothesis_sampler_manifest"] = str(hyp_sampler_manifest_out)
        artifacts["hypothesis_fused_report"] = str(hyp_fused_out)
        artifacts["hypothesis_fused_rows"] = str(hyp_fused_rows_out)
    _finalize_manifest(
        manifest_out=manifest_out,
        run_id=run_id,
        args=args,
        steps=steps,
        status="success",
        artifacts=artifacts,
    )
    print(f"hybrid orchestrator manifest: {manifest_out}")
    return 0


def _finalize_manifest(
    *,
    manifest_out: Path,
    run_id: str,
    args: argparse.Namespace,
    steps: list[StepResult],
    status: str,
    artifacts: dict[str, str],
) -> None:
    payload = {
        "schema": "dgx_spark_hybrid_orchestrator.v1",
        "run_id": run_id,
        "generated_at_utc": _utc_now(),
        "workspace_root": str(REPO_ROOT),
        "status": status,
        "profile": args.profile,
        "config": {
            "center": args.center,
            "mode": args.mode,
            "dry_run": bool(args.dry_run),
            "skip_locked_build": bool(args.skip_locked_build),
            "skip_dataset": bool(args.skip_dataset),
            "skip_train": bool(args.skip_train),
            "skip_rerank": bool(args.skip_rerank),
            "with_hypothesis_loop": bool(args.with_hypothesis_loop),
            "skip_hypothesis_sampler": bool(args.skip_hypothesis_sampler),
            "skip_hypothesis_fuser": bool(args.skip_hypothesis_fuser),
            "hyp_goal": str(args.hyp_goal),
            "hyp_goal_file": str(args.hyp_goal_file),
            "hyp_input_candidates": str(args.hyp_input_candidates),
            "hyp_top_k": int(args.hyp_top_k),
            "hyp_max_pass": int(args.hyp_max_pass),
            "hyp_emit_skills": bool(args.hyp_emit_skills),
            "hyp_strict_check": bool(args.hyp_strict_check),
            "hyp_skip_lean_gate": bool(args.hyp_skip_lean_gate),
        },
        "steps": [asdict(s) for s in steps],
        "artifacts": artifacts,
    }
    manifest_out.parent.mkdir(parents=True, exist_ok=True)
    manifest_out.write_text(json.dumps(payload, indent=2, ensure_ascii=True) + "\n", encoding="utf-8")


if __name__ == "__main__":
    raise SystemExit(main())
