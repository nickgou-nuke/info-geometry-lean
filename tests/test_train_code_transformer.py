from __future__ import annotations

import hashlib
import json

import pytest

torch = pytest.importorskip("torch")

from tools.repository_evolution.latent_taxonomy import _canonical_embedding_packet_digest
from tools.repository_evolution.train_code_transformer import (
    _apply_rotary_position_encoding,
    train_code_transformer,
)
from tools.repository_evolution.train_taxonomy_baseline import train_taxonomy_baseline


def _rebind_corpus_digest(corpus):
    payload = b"".join(
        (json.dumps(row, sort_keys=True, ensure_ascii=False) + "\n").encode()
        for row in corpus["rows"]
    )
    corpus["corpusRowsSha256"] = hashlib.sha256(payload).hexdigest()


@pytest.mark.parametrize("position_encoding", ["learned_absolute", "rotary"])
def test_small_transformer_trains_on_train_groups_and_exports_bound_embeddings(
        tmp_path, position_encoding):
    from tests.test_train_taxonomy_baseline import _fixtures

    source_map, corpus, _ = _fixtures()
    texts = []
    for row in corpus["rows"]:
        marker = f"TRAIN_TOKEN_{row['artifactId']}" if row["split"] == "train" else (
            f"HELDOUT_ONLY_{row['artifactId']}")
        source = f"namespace Example\n theorem {marker} : True := by trivial\n"
        path = tmp_path / row["artifactId"]
        path.parent.mkdir(parents=True, exist_ok=True)
        path.write_text(source, encoding="utf-8")
        digest = hashlib.sha256(source.encode()).hexdigest()
        row["sourceSha256"] = digest
        row["modelInput"] = {"sourceText": source}
        texts.append((row["artifactId"], digest))
        file_row = next(item for item in source_map["files"]
                        if item["path"] == row["artifactId"])
        file_row["contentSha256"] = digest
    _rebind_corpus_digest(corpus)

    packet, checkpoint, report = train_code_transformer(
        source_map, corpus, tmp_path, dimension=8, heads=2, layers=1,
        max_length=24, max_vocab=64, epochs=1, batch_size=4,
        learning_rate=1e-3, seed=3, device="cpu",
        position_encoding=position_encoding,
    )
    assert packet["encoderTraining"]["dataScope"] == "repository_train_split"
    assert packet["encoderTraining"]["trainingSplitGroupsSha256"]
    assert len(packet["embeddings"]) == len(corpus["rows"])
    assert all(len(row["vector"]) == 8 for row in packet["embeddings"])
    assert "HELDOUT_ONLY" not in dict(checkpoint["vocabulary"])
    assert report["trainingArtifactCount"] == 4
    assert report["trainingDataScope"] == "train_split_source_only_no_labels_or_heldout_source"
    assert checkpoint["config"]["positionEncoding"] == position_encoding
    assert checkpoint["config"]["attentionDirection"] == "bidirectional"
    assert report["positionEncoding"] == position_encoding
    assert report["epochMaskedTokenLoss"] and all(
        value >= 0 for value in report["epochMaskedTokenLoss"])
    assert packet["packetSha256"] == _canonical_embedding_packet_digest(packet)
    classifier, evaluation = train_taxonomy_baseline(
        source_map, corpus, packet, latent_dimension=2, max_iterations=4000,
    )
    assert classifier["encoderSpec"]["version"] == packet["encoderVersion"]
    assert evaluation["encoderPacketSha256"] == packet["packetSha256"]


def test_rotary_encoding_preserves_query_key_scores_under_common_position_shift():
    torch.manual_seed(2)
    query = torch.randn(1, 2, 5, 8)
    key = torch.randn(1, 2, 5, 8)
    positions = torch.arange(5, dtype=torch.float32)
    shifted = positions + 13
    score = (_apply_rotary_position_encoding(query, positions)
             * _apply_rotary_position_encoding(key, positions)).sum(-1)
    shifted_score = (_apply_rotary_position_encoding(query, shifted)
                     * _apply_rotary_position_encoding(key, shifted)).sum(-1)
    torch.testing.assert_close(score, shifted_score, rtol=1e-5, atol=1e-5)


def test_rotary_encoder_rejects_odd_head_dimension():
    from tests.test_train_taxonomy_baseline import _fixtures

    source_map, corpus, _ = _fixtures()
    with pytest.raises(ValueError, match="even per-head dimension"):
        train_code_transformer(source_map, corpus, dimension=10, heads=2,
                               position_encoding="rotary")


def test_transformer_refuses_a_non_ready_reviewed_corpus():
    from tests.test_train_taxonomy_baseline import _fixtures

    source_map, corpus, _ = _fixtures()
    corpus["rows"][0]["labelSetCompleteByFacet"]["artifact_role"] = False
    _rebind_corpus_digest(corpus)
    with pytest.raises(ValueError, match="not ready"):
        train_code_transformer(source_map, corpus)


def test_transformer_rejects_training_text_that_does_not_match_source_hash(tmp_path):
    from tests.test_train_taxonomy_baseline import _fixtures

    source_map, corpus, _ = _fixtures()
    for row in corpus["rows"]:
        if row["split"] != "train":
            continue
        text = f"namespace Example\n theorem {row['artifactId'].replace('/', '_')} : True := by trivial\n"
        digest = hashlib.sha256(text.encode()).hexdigest()
        row["sourceSha256"] = digest
        row["modelInput"] = {"sourceText": text}
        next(item for item in source_map["files"]
             if item["path"] == row["artifactId"])["contentSha256"] = digest
    row = next(item for item in corpus["rows"] if item["split"] == "train")
    row["modelInput"] = {"sourceText": "stale, unbound source"}
    _rebind_corpus_digest(corpus)
    with pytest.raises(ValueError, match="training text digest differs"):
        train_code_transformer(source_map, corpus, tmp_path)
