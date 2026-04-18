#!/usr/bin/env python3
from __future__ import annotations

import argparse
import json
import math
import random
import sys
from dataclasses import dataclass
from pathlib import Path
from typing import Any

import numpy as np

REPO_ROOT = Path(__file__).resolve().parents[2]
if str(REPO_ROOT) not in sys.path:
    sys.path.insert(0, str(REPO_ROOT))

from tools.infra.link_scorer_common import (
    FeaturizerConfig,
    binary_auc,
    row_to_sparse_features,
    sigmoid,
    sparse_dot,
    weighted_accuracy,
    weighted_logloss,
)


DEFAULT_DATASET = "reports/training/link_ats_dataset.jsonl"
DEFAULT_MODEL_OUT = "reports/training/link_scorer_model.npz"
DEFAULT_METRICS_OUT = "reports/training/link_scorer_metrics.json"


@dataclass
class Example:
    id: str
    split: str
    label: int
    weight: float
    feats: dict[int, float]


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


def _to_examples(
    rows: list[dict[str, Any]],
    *,
    feat_cfg: FeaturizerConfig,
    max_rows: int,
) -> list[Example]:
    out: list[Example] = []
    for row in rows:
        split = str(row.get("split", "")).strip() or "train"
        label = 1 if int(row.get("label", 0)) == 1 else 0
        weight_raw = row.get("weight", 1.0)
        weight = float(weight_raw) if isinstance(weight_raw, (int, float)) else 1.0
        ex = Example(
            id=str(row.get("id", "")).strip(),
            split=split,
            label=label,
            weight=max(0.0, weight),
            feats=row_to_sparse_features(row, feat_cfg),
        )
        out.append(ex)
        if max_rows > 0 and len(out) >= max_rows:
            break
    return out


def _predict_probs(examples: list[Example], weights: np.ndarray, bias: float) -> list[float]:
    out: list[float] = []
    for ex in examples:
        z = bias + sparse_dot(weights, ex.feats)
        out.append(sigmoid(z))
    return out


def _eval_split(examples: list[Example], weights: np.ndarray, bias: float) -> dict[str, float]:
    if not examples:
        return {"count": 0.0, "logloss": 0.0, "accuracy": 0.0, "auc": 0.5}
    probs = _predict_probs(examples, weights, bias)
    labels = [ex.label for ex in examples]
    sample_weights = [ex.weight for ex in examples]
    return {
        "count": float(len(examples)),
        "logloss": float(weighted_logloss(probs, labels, sample_weights)),
        "accuracy": float(weighted_accuracy(probs, labels, sample_weights)),
        "auc": float(binary_auc(probs, labels)),
    }


def parse_args() -> argparse.Namespace:
    ap = argparse.ArgumentParser(
        description=(
            "Train a local hashed-feature logistic link scorer over ATS dataset rows. "
            "No external ML frameworks required."
        )
    )
    ap.add_argument("--dataset", default=DEFAULT_DATASET)
    ap.add_argument("--model-out", default=DEFAULT_MODEL_OUT)
    ap.add_argument("--metrics-out", default=DEFAULT_METRICS_OUT)
    ap.add_argument("--dim", type=int, default=262144)
    ap.add_argument("--hash-seed", type=int, default=20260418)
    ap.add_argument("--text-token-limit", type=int, default=32)
    ap.add_argument("--epochs", type=int, default=6)
    ap.add_argument("--learning-rate", type=float, default=0.05)
    ap.add_argument("--l2", type=float, default=1e-6)
    ap.add_argument("--grad-clip", type=float, default=5.0)
    ap.add_argument("--max-abs-weight", type=float, default=8.0)
    ap.add_argument("--seed", type=int, default=20260418)
    ap.add_argument("--max-rows", type=int, default=0, help="0 means use all rows.")
    ap.add_argument(
        "--train-splits",
        default="train",
        help="Comma-separated split labels used for optimization.",
    )
    ap.add_argument(
        "--val-splits",
        default="val",
        help="Comma-separated split labels used for early monitoring.",
    )
    ap.add_argument(
        "--test-splits",
        default="test",
        help="Comma-separated split labels reported after training.",
    )
    return ap.parse_args()


def main() -> int:
    args = parse_args()
    rng = random.Random(args.seed)

    dataset_path = Path(args.dataset).resolve()
    model_out = Path(args.model_out).resolve()
    metrics_out = Path(args.metrics_out).resolve()
    if not dataset_path.exists():
        raise FileNotFoundError(f"dataset not found: {dataset_path}")
    if args.dim <= 0:
        raise ValueError("--dim must be > 0")

    feat_cfg = FeaturizerConfig(
        dim=args.dim,
        hash_seed=args.hash_seed,
        text_token_limit=max(1, args.text_token_limit),
    )

    rows = _iter_jsonl(dataset_path)
    examples = _to_examples(rows, feat_cfg=feat_cfg, max_rows=max(0, args.max_rows))
    if not examples:
        raise RuntimeError("no valid rows loaded from dataset")

    train_splits = {x.strip() for x in args.train_splits.split(",") if x.strip()}
    val_splits = {x.strip() for x in args.val_splits.split(",") if x.strip()}
    test_splits = {x.strip() for x in args.test_splits.split(",") if x.strip()}

    train_rows = [ex for ex in examples if ex.split in train_splits]
    val_rows = [ex for ex in examples if ex.split in val_splits]
    test_rows = [ex for ex in examples if ex.split in test_splits]

    if not train_rows:
        raise RuntimeError("empty train split after filtering; adjust --train-splits")

    weights = np.zeros((args.dim,), dtype=np.float64)
    bias = 0.0

    history: list[dict[str, Any]] = []
    lr0 = float(args.learning_rate)
    l2 = float(args.l2)
    grad_clip = max(0.0, float(args.grad_clip))
    max_abs_weight = max(0.0, float(args.max_abs_weight))

    for epoch in range(1, max(1, args.epochs) + 1):
        idxs = list(range(len(train_rows)))
        rng.shuffle(idxs)
        lr = lr0 / math.sqrt(float(epoch))

        for j in idxs:
            ex = train_rows[j]
            z = bias + sparse_dot(weights, ex.feats)
            p = sigmoid(z)
            err = p - float(ex.label)
            grad_scale = ex.weight * err
            if grad_clip > 0.0:
                if grad_scale > grad_clip:
                    grad_scale = grad_clip
                elif grad_scale < -grad_clip:
                    grad_scale = -grad_clip

            for idx, val in ex.feats.items():
                if idx < 0 or idx >= weights.shape[0]:
                    continue
                weights[idx] -= lr * ((grad_scale * val) + (l2 * weights[idx]))
                if max_abs_weight > 0.0:
                    if weights[idx] > max_abs_weight:
                        weights[idx] = max_abs_weight
                    elif weights[idx] < -max_abs_weight:
                        weights[idx] = -max_abs_weight
            bias -= lr * grad_scale
            if max_abs_weight > 0.0:
                if bias > max_abs_weight:
                    bias = max_abs_weight
                elif bias < -max_abs_weight:
                    bias = -max_abs_weight

        train_metrics = _eval_split(train_rows, weights, bias)
        val_metrics = _eval_split(val_rows, weights, bias)
        row = {
            "epoch": epoch,
            "learning_rate": lr,
            "train": train_metrics,
            "val": val_metrics,
        }
        history.append(row)
        print(
            f"epoch={epoch} lr={lr:.6f} "
            f"train(loss={train_metrics['logloss']:.4f}, auc={train_metrics['auc']:.4f}) "
            f"val(loss={val_metrics['logloss']:.4f}, auc={val_metrics['auc']:.4f})"
        )

    final_train = _eval_split(train_rows, weights, bias)
    final_val = _eval_split(val_rows, weights, bias)
    final_test = _eval_split(test_rows, weights, bias)

    model_out.parent.mkdir(parents=True, exist_ok=True)
    np.savez_compressed(
        model_out,
        weights=weights.astype(np.float32),
        bias=np.array([bias], dtype=np.float32),
        dim=np.array([feat_cfg.dim], dtype=np.int64),
        hash_seed=np.array([feat_cfg.hash_seed], dtype=np.int64),
        text_token_limit=np.array([feat_cfg.text_token_limit], dtype=np.int64),
        model_version=np.array([1], dtype=np.int64),
    )

    metrics = {
        "dataset": str(dataset_path),
        "model_out": str(model_out),
        "model": {
            "version": 1,
            "type": "hashed_logistic_regression",
            "dim": feat_cfg.dim,
            "hash_seed": feat_cfg.hash_seed,
            "text_token_limit": feat_cfg.text_token_limit,
        },
        "train_config": {
            "epochs": args.epochs,
            "learning_rate": args.learning_rate,
            "l2": args.l2,
            "grad_clip": args.grad_clip,
            "max_abs_weight": args.max_abs_weight,
            "seed": args.seed,
            "max_rows": args.max_rows,
            "train_splits": sorted(train_splits),
            "val_splits": sorted(val_splits),
            "test_splits": sorted(test_splits),
        },
        "counts": {
            "total_rows": len(examples),
            "train_rows": len(train_rows),
            "val_rows": len(val_rows),
            "test_rows": len(test_rows),
        },
        "history": history,
        "final": {
            "train": final_train,
            "val": final_val,
            "test": final_test,
        },
    }
    metrics_out.parent.mkdir(parents=True, exist_ok=True)
    metrics_out.write_text(json.dumps(metrics, indent=2, ensure_ascii=True) + "\n", encoding="utf-8")

    print(f"saved model:   {model_out}")
    print(f"saved metrics: {metrics_out}")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
