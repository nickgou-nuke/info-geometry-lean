#!/usr/bin/env python3
from __future__ import annotations

import argparse
import json
import sys
from pathlib import Path
from typing import Any

import numpy as np

REPO_ROOT = Path(__file__).resolve().parents[2]
if str(REPO_ROOT) not in sys.path:
    sys.path.insert(0, str(REPO_ROOT))

from tools.infra.link_scorer_common import FeaturizerConfig, row_to_sparse_features, sigmoid, sparse_dot


DEFAULT_MODEL = "reports/training/link_scorer_model.npz"
DEFAULT_INPUT = "reports/training/link_ats_dataset.jsonl"
DEFAULT_OUT = "reports/training/link_candidate_scores.jsonl"


def _iter_jsonl(path: Path) -> list[dict[str, Any]]:
    rows: list[dict[str, Any]] = []
    if not path.exists():
        return rows
    with path.open("r", encoding="utf-8") as handle:
        for raw in handle:
            line = raw.strip()
            if not line:
                continue
            try:
                row = json.loads(line)
            except Exception:
                continue
            if isinstance(row, dict):
                rows.append(row)
    return rows


def _load_model(path: Path) -> tuple[np.ndarray, float, FeaturizerConfig]:
    if not path.exists():
        raise FileNotFoundError(f"model not found: {path}")
    payload = np.load(path, allow_pickle=False)
    weights = payload["weights"].astype(np.float64)
    bias = float(payload["bias"][0])
    dim = int(payload["dim"][0])
    hash_seed = int(payload["hash_seed"][0])
    text_token_limit = int(payload["text_token_limit"][0])
    cfg = FeaturizerConfig(dim=dim, hash_seed=hash_seed, text_token_limit=text_token_limit)
    if weights.shape[0] != dim:
        raise RuntimeError(f"model mismatch: weights len={weights.shape[0]} dim={dim}")
    return weights, bias, cfg


def parse_args() -> argparse.Namespace:
    ap = argparse.ArgumentParser(
        description=(
            "Score/rerank link candidates with a local hashed logistic scorer model "
            "trained by train_link_scorer.py."
        )
    )
    ap.add_argument("--model", default=DEFAULT_MODEL)
    ap.add_argument("--input", default=DEFAULT_INPUT)
    ap.add_argument("--out", default=DEFAULT_OUT)
    ap.add_argument("--top-k", type=int, default=0, help="0 means write all rows.")
    ap.add_argument(
        "--sort-by",
        default="score",
        choices=["score", "logit"],
        help="Field used for ranking when --top-k > 0.",
    )
    return ap.parse_args()


def main() -> int:
    args = parse_args()
    model_path = Path(args.model).resolve()
    input_path = Path(args.input).resolve()
    out_path = Path(args.out).resolve()

    weights, bias, feat_cfg = _load_model(model_path)
    rows = _iter_jsonl(input_path)
    if not rows:
        raise RuntimeError(f"no rows loaded from input: {input_path}")

    scored: list[dict[str, Any]] = []
    for row in rows:
        feats = row_to_sparse_features(row, feat_cfg)
        logit = bias + sparse_dot(weights, feats)
        score = sigmoid(logit)
        new_row = dict(row)
        new_row["scorer"] = {
            "model_path": str(model_path),
            "score": float(score),
            "logit": float(logit),
        }
        scored.append(new_row)

    key = "score" if args.sort_by == "score" else "logit"
    scored.sort(key=lambda r: float(r.get("scorer", {}).get(key, 0.0)), reverse=True)
    if args.top_k > 0:
        scored = scored[: args.top_k]

    for rank, row in enumerate(scored, start=1):
        row.setdefault("scorer", {})
        row["scorer"]["rank"] = rank

    out_path.parent.mkdir(parents=True, exist_ok=True)
    with out_path.open("w", encoding="utf-8") as handle:
        for row in scored:
            handle.write(json.dumps(row, ensure_ascii=True) + "\n")

    print(f"loaded model: {model_path}")
    print(f"input rows:   {len(rows)}")
    print(f"written rows: {len(scored)}")
    print(f"output file:  {out_path}")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
