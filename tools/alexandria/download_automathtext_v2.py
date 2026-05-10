#!/usr/bin/env python3
from __future__ import annotations

import argparse
import json
import os
from dataclasses import asdict, dataclass
from pathlib import Path
from typing import Iterable


DATASET_REPO = "OpenSQZ/AutoMathText-V2"
DEFAULT_LOCAL_DIR = Path("external/automathtext-v2")
DEFAULT_CONFIGS = ("math_web", "megamath", "reasoning_qa")


@dataclass(frozen=True)
class DownloadPlan:
    dataset: str
    local_dir: str
    revision: str
    mode: str
    configs: list[str]
    quality_buckets: list[str]
    allow_patterns: list[str]
    ignore_patterns: list[str]
    allow_full: bool
    token_file: str | None


def normalize_config(config: str) -> str:
    return config.strip().strip("/")


def pattern_for_config(config: str, quality_buckets: Iterable[str]) -> list[str]:
    config = normalize_config(config)
    buckets = [bucket.strip().strip("/") for bucket in quality_buckets if bucket.strip()]
    if buckets:
        return [f"{config}/{bucket}/*.parquet" for bucket in buckets]
    return [f"{config}/**/*.parquet", f"{config}/*.parquet"]


def build_allow_patterns(
    *,
    mode: str,
    configs: list[str],
    quality_buckets: list[str],
    extra_allow: list[str],
    allow_full: bool,
) -> list[str]:
    if mode == "full":
        if not allow_full:
            raise SystemExit("Refusing full AutoMathText-V2 mirror without --allow-full.")
        return []
    if mode == "metadata":
        return ["README.md", "LICENSE*", "*.md", "*.json", "*.yaml", "*.yml"]
    patterns: list[str] = []
    for config in configs:
        patterns.extend(pattern_for_config(config, quality_buckets))
    patterns.extend(extra_allow)
    return list(dict.fromkeys(patterns))


def make_plan(args: argparse.Namespace) -> DownloadPlan:
    configs = [normalize_config(value) for value in args.config]
    if args.default_operator_configs:
        configs.extend(DEFAULT_CONFIGS)
    configs = list(dict.fromkeys(config for config in configs if config))
    allow_patterns = build_allow_patterns(
        mode=args.mode,
        configs=configs,
        quality_buckets=args.quality_bucket,
        extra_allow=args.allow_pattern,
        allow_full=args.allow_full,
    )
    return DownloadPlan(
        dataset=args.dataset,
        local_dir=str(Path(args.local_dir)),
        revision=args.revision,
        mode=args.mode,
        configs=configs,
        quality_buckets=args.quality_bucket,
        allow_patterns=allow_patterns,
        ignore_patterns=args.ignore_pattern,
        allow_full=bool(args.allow_full),
        token_file=str(args.token_file) if args.token_file else None,
    )


def import_huggingface_hub():
    try:
        from huggingface_hub import HfApi, snapshot_download
    except ImportError as exc:
        raise SystemExit("Missing dependency: install `huggingface_hub` in the repo venv.") from exc
    return HfApi, snapshot_download


def write_json(path: Path, obj: object) -> None:
    path.parent.mkdir(parents=True, exist_ok=True)
    path.write_text(json.dumps(obj, ensure_ascii=True, indent=2, sort_keys=True) + "\n", encoding="utf-8")


def read_token(plan: DownloadPlan) -> str | None:
    if not plan.token_file:
        return None
    path = Path(plan.token_file)
    if not path.exists():
        raise SystemExit(f"Token file does not exist: {path}")
    token = path.read_text(encoding="utf-8").strip()
    return token or None


def list_manifest(plan: DownloadPlan, *, limit: int | None) -> dict[str, object]:
    HfApi, _ = import_huggingface_hub()
    token = read_token(plan)
    api = HfApi(token=token)
    files = list(api.list_repo_files(plan.dataset, repo_type="dataset", revision=plan.revision, token=token))
    matched = []
    if plan.allow_patterns:
        import fnmatch

        for file in files:
            if any(fnmatch.fnmatch(file, pattern) for pattern in plan.allow_patterns):
                matched.append(file)
    else:
        matched = files
    if limit is not None:
        shown = matched[:limit]
    else:
        shown = matched
    return {
        "dataset": plan.dataset,
        "revision": plan.revision,
        "mode": plan.mode,
        "totalFiles": len(files),
        "matchedFiles": len(matched),
        "shownFiles": shown,
        "allowPatterns": plan.allow_patterns,
        "ignorePatterns": plan.ignore_patterns,
    }


def run_download(plan: DownloadPlan) -> str:
    _, snapshot_download = import_huggingface_hub()
    token = read_token(plan)
    if token:
        os.environ["HF_TOKEN"] = token
        os.environ["HUGGINGFACE_HUB_TOKEN"] = token
    local_dir = Path(plan.local_dir)
    local_dir.mkdir(parents=True, exist_ok=True)
    kwargs = {
        "repo_id": plan.dataset,
        "repo_type": "dataset",
        "revision": plan.revision,
        "local_dir": local_dir.as_posix(),
        "local_dir_use_symlinks": False,
        "resume_download": True,
    }
    if token:
        kwargs["token"] = token
    if plan.allow_patterns:
        kwargs["allow_patterns"] = plan.allow_patterns
    if plan.ignore_patterns:
        kwargs["ignore_patterns"] = plan.ignore_patterns
    path = snapshot_download(**kwargs)
    return str(path)


def parse_args() -> argparse.Namespace:
    parser = argparse.ArgumentParser(description="Plan or download AutoMathText-V2 shards into external/ safely.")
    parser.add_argument("--dataset", default=DATASET_REPO)
    parser.add_argument("--local-dir", default=str(DEFAULT_LOCAL_DIR))
    parser.add_argument("--revision", default="main")
    parser.add_argument("--mode", choices=["metadata", "domain", "full"], default="metadata")
    parser.add_argument("--config", action="append", default=[], help="dataset config/domain folder, e.g. math_web")
    parser.add_argument("--default-operator-configs", action="store_true", help="include math_web, megamath, reasoning_qa")
    parser.add_argument("--quality-bucket", action="append", default=[], help="quality bucket path, e.g. 90-100")
    parser.add_argument("--allow-pattern", action="append", default=[], help="extra HuggingFace allow_pattern")
    parser.add_argument("--ignore-pattern", action="append", default=[], help="extra HuggingFace ignore_pattern")
    parser.add_argument("--allow-full", action="store_true", help="required for --mode full")
    parser.add_argument("--token-file", type=Path, help="file containing a HuggingFace token; never printed")
    parser.add_argument("--manifest", action="store_true", help="list matched files instead of downloading")
    parser.add_argument("--manifest-limit", type=int, default=80)
    parser.add_argument("--json-out", type=Path)
    return parser.parse_args()


def main() -> int:
    args = parse_args()
    plan = make_plan(args)
    if args.manifest:
        out = list_manifest(plan, limit=args.manifest_limit)
        out["plan"] = asdict(plan)
        rendered = json.dumps(out, ensure_ascii=True, indent=2, sort_keys=True)
        if args.json_out:
            write_json(args.json_out, out)
        else:
            print(rendered)
        return 0
    downloaded_to = run_download(plan)
    out = {"downloadedTo": downloaded_to, "plan": asdict(plan)}
    if args.json_out:
        write_json(args.json_out, out)
    else:
        print(json.dumps(out, ensure_ascii=True, indent=2, sort_keys=True))
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
