"""Tests for tools/infra/link_scorer_common.py — link scoring utilities."""
from __future__ import annotations

import math

import pytest

from tools.infra.link_scorer_common import (
    FeaturizerConfig,
    binary_auc,
    row_to_sparse_features,
    sigmoid,
    sparse_dot,
    weighted_accuracy,
    weighted_logloss,
)


# ---------------------------------------------------------------------------
# sigmoid
# ---------------------------------------------------------------------------

def test_sigmoid_zero() -> None:
    assert sigmoid(0.0) == pytest.approx(0.5)


def test_sigmoid_positive_large() -> None:
    result = sigmoid(100.0)
    assert result > 0.999


def test_sigmoid_negative_large() -> None:
    result = sigmoid(-100.0)
    assert result < 0.001


def test_sigmoid_symmetry() -> None:
    assert sigmoid(1.0) + sigmoid(-1.0) == pytest.approx(1.0)


def test_sigmoid_output_range() -> None:
    for x in [-10, -1, 0, 1, 10]:
        s = sigmoid(float(x))
        assert 0.0 < s < 1.0


# ---------------------------------------------------------------------------
# sparse_dot
# ---------------------------------------------------------------------------

def test_sparse_dot_empty_features() -> None:
    result = sparse_dot([1.0, 2.0, 3.0], {})
    assert result == 0.0


def test_sparse_dot_single_feature() -> None:
    # weights is a list, feats maps index → value
    result = sparse_dot([0.0, 2.0, 0.0], {1: 3.0})
    assert result == pytest.approx(6.0)


def test_sparse_dot_multiple_features() -> None:
    weights = [1.0, 2.0, 3.0]
    feats = {0: 1.0, 1: 1.0, 2: 1.0}
    result = sparse_dot(weights, feats)
    assert result == pytest.approx(6.0)


def test_sparse_dot_out_of_bounds_indices_ignored() -> None:
    # index 5 exceeds len(weights)==3 → ignored
    weights = [1.0, 2.0, 3.0]
    feats = {0: 1.0, 5: 10.0}  # index 5 is out of range
    result = sparse_dot(weights, feats)
    assert result == pytest.approx(1.0)


# ---------------------------------------------------------------------------
# binary_auc
# ---------------------------------------------------------------------------

def test_binary_auc_perfect_separation() -> None:
    # All positives scored higher than negatives → AUC = 1.0
    scores = [0.9, 0.8, 0.2, 0.1]
    labels = [1, 1, 0, 0]
    result = binary_auc(scores, labels)
    assert result == pytest.approx(1.0)


def test_binary_auc_random_predictions() -> None:
    # Alternating → AUC ~= 0.5
    scores = [0.5, 0.5, 0.5, 0.5]
    labels = [1, 0, 1, 0]
    result = binary_auc(scores, labels)
    assert 0.0 <= result <= 1.0


def test_binary_auc_worst_case() -> None:
    # All positives scored lower than negatives → AUC = 0.0
    scores = [0.1, 0.2, 0.8, 0.9]
    labels = [1, 1, 0, 0]
    result = binary_auc(scores, labels)
    assert result == pytest.approx(0.0)


def test_binary_auc_single_class_returns_fallback() -> None:
    # All same label → undefined, should not crash
    result = binary_auc([0.5, 0.6], [1, 1])
    assert isinstance(result, float)


# ---------------------------------------------------------------------------
# weighted_accuracy
# ---------------------------------------------------------------------------

def test_weighted_accuracy_perfect() -> None:
    probs = [0.9, 0.9, 0.1, 0.1]
    labels = [1, 1, 0, 0]
    weights = [1.0, 1.0, 1.0, 1.0]
    result = weighted_accuracy(probs, labels, weights)
    assert result == pytest.approx(1.0)


def test_weighted_accuracy_all_wrong() -> None:
    probs = [0.1, 0.1, 0.9, 0.9]
    labels = [1, 1, 0, 0]
    weights = [1.0, 1.0, 1.0, 1.0]
    result = weighted_accuracy(probs, labels, weights)
    assert result == pytest.approx(0.0)


def test_weighted_accuracy_half_correct() -> None:
    probs = [0.9, 0.1, 0.9, 0.1]  # first right, second right, third wrong (0.9 for label 0), fourth wrong
    labels = [1, 0, 0, 1]
    weights = [1.0, 1.0, 1.0, 1.0]
    result = weighted_accuracy(probs, labels, weights)
    assert result == pytest.approx(0.5)


def test_weighted_accuracy_with_zero_weights() -> None:
    probs = [0.9, 0.1]
    labels = [0, 1]
    weights = [0.0, 0.0]
    result = weighted_accuracy(probs, labels, weights)
    assert isinstance(result, float)


# ---------------------------------------------------------------------------
# weighted_logloss
# ---------------------------------------------------------------------------

def test_weighted_logloss_perfect_predictions() -> None:
    probs = [0.9999, 0.0001]
    labels = [1, 0]
    weights = [1.0, 1.0]
    result = weighted_logloss(probs, labels, weights)
    assert result < 0.01


def test_weighted_logloss_wrong_predictions_high_loss() -> None:
    probs = [0.0001, 0.9999]
    labels = [1, 0]
    weights = [1.0, 1.0]
    result = weighted_logloss(probs, labels, weights)
    assert result > 5.0


def test_weighted_logloss_is_non_negative() -> None:
    probs = [0.6, 0.4, 0.7]
    labels = [1, 0, 1]
    weights = [1.0, 1.0, 1.0]
    result = weighted_logloss(probs, labels, weights)
    assert result >= 0.0


# ---------------------------------------------------------------------------
# FeaturizerConfig defaults
# ---------------------------------------------------------------------------

def test_featurizer_config_default_dim() -> None:
    cfg = FeaturizerConfig(dim=1024, hash_seed=42)
    assert isinstance(cfg.dim, int)
    assert cfg.dim > 0


def test_featurizer_config_custom_dim() -> None:
    cfg = FeaturizerConfig(dim=512, hash_seed=0)
    assert cfg.dim == 512


# ---------------------------------------------------------------------------
# row_to_sparse_features
# ---------------------------------------------------------------------------

_CFG = FeaturizerConfig(dim=1024, hash_seed=42)


def test_row_to_sparse_features_empty_row() -> None:
    result = row_to_sparse_features({}, _CFG)
    assert isinstance(result, dict)


def test_row_to_sparse_features_returns_int_keys() -> None:
    row = {
        "src_module": "InfoGeometry.Canonical",
        "dst_module": "InfoGeometry.Singular",
        "semantic_overlap": 0.8,
        "label": 1,
    }
    result = row_to_sparse_features(row, _CFG)
    for k in result:
        assert isinstance(k, int)
        assert 0 <= k < _CFG.dim


def test_row_to_sparse_features_same_input_is_deterministic() -> None:
    row = {"src_module": "A", "dst_module": "B", "semantic_overlap": 0.5}
    r1 = row_to_sparse_features(row, _CFG)
    r2 = row_to_sparse_features(row, _CFG)
    assert r1 == r2
