#!/usr/bin/env python3
"""Train a small source-only denoising Transformer and export artifact vectors.

This is an optional self-supervised encoder stage. Vocabulary and weights are
learned from reviewed-corpus train groups only. It does not consume taxonomy
labels, Git messages, held-out source, or dependency neighborhoods. The output
packet can be passed to ``train_taxonomy_baseline.py`` for reviewed-label
fine-tuning/evaluation.
"""
from __future__ import annotations

import argparse
import gzip
import hashlib
import json
import math
import re
import sys
from pathlib import Path
from typing import Any

_REPOSITORY_ROOT = Path(__file__).resolve().parents[2]
if str(_REPOSITORY_ROOT) not in sys.path:
    sys.path.insert(0, str(_REPOSITORY_ROOT))

from tools.repository_evolution.latent_taxonomy import build_encoder_embedding_packet
from tools.repository_evolution.refactoring_map import ROOT, SOURCE_SUFFIXES
from tools.repository_evolution.taxonomy_training_readiness import audit_training_readiness


TOKEN_PATTERN = re.compile(r"[A-Za-z_][A-Za-z_0-9']*|[0-9]+|[^\s]", re.UNICODE)
PAD, MASK, UNK, CLS = "<pad>", "<mask>", "<unk>", "<cls>"
MODEL_VERSION = "repository_source_denoising_transformer.v2"


def _apply_rotary_position_encoding(values: Any, positions: Any, *, base: float = 10000.0) -> Any:
    """Apply pairwise RoPE to ``[batch, heads, sequence, head_dim]`` tensors.

    This numerical implementation follows the relative-position law proved by
    the Lean RoPE owners. It is deliberately separate from those proofs: the
    Lean results do not certify PyTorch execution or its floating-point error.
    """
    import torch

    head_dimension = values.shape[-1]
    if head_dimension % 2:
        raise ValueError("rotary attention requires an even per-head dimension")
    if not math.isfinite(base) or base <= 1.0:
        raise ValueError("rotary base must be finite and greater than one")
    frequencies = torch.arange(
        0, head_dimension, 2, dtype=values.dtype, device=values.device,
    ) / head_dimension
    inverse_frequencies = base ** (-frequencies)
    angles = positions.to(device=values.device, dtype=values.dtype).unsqueeze(-1)
    angles = angles * inverse_frequencies
    cosine = angles.cos()[None, None, :, :]
    sine = angles.sin()[None, None, :, :]
    pairs = values.reshape(*values.shape[:-1], head_dimension // 2, 2)
    even, odd = pairs.unbind(dim=-1)
    return torch.stack((even * cosine - odd * sine,
                        even * sine + odd * cosine), dim=-1).flatten(-2)


def _read_json(path: Path) -> dict[str, Any]:
    opener = gzip.open if path.suffix == ".gz" else open
    with opener(path, "rt", encoding="utf-8") as stream:
        value = json.load(stream)
    if not isinstance(value, dict):
        raise ValueError(f"{path}: expected a JSON object")
    return value


def _write_json(path: Path, value: dict[str, Any]) -> None:
    path.parent.mkdir(parents=True, exist_ok=True)
    opener = gzip.open if path.suffix == ".gz" else open
    with opener(path, "wt", encoding="utf-8") as stream:
        stream.write(json.dumps(value, sort_keys=True, ensure_ascii=False) + "\n")


def _sha256(path: Path) -> str:
    digest = hashlib.sha256()
    with path.open("rb") as stream:
        for block in iter(lambda: stream.read(1024 * 1024), b""):
            digest.update(block)
    return digest.hexdigest()


def _tokenize(text: str) -> list[str]:
    return TOKEN_PATTERN.findall(text)


def _train_group_digest(rows: list[dict[str, Any]]) -> str:
    groups = sorted({row["splitGroup"] for row in rows if row.get("split") == "train"})
    payload = json.dumps(groups, ensure_ascii=False, separators=(",", ":")).encode("utf-8")
    return hashlib.sha256(payload).hexdigest()


def _training_rows(corpus: dict[str, Any]) -> list[dict[str, Any]]:
    rows = corpus.get("rows")
    if not isinstance(rows, list):
        raise ValueError("reviewed corpus must contain rows")
    train = [row for row in rows if isinstance(row, dict) and row.get("split") == "train"]
    if len(train) < 2:
        raise ValueError("self-supervised encoder training needs at least two train artifacts")
    for row in train:
        if row.get("provenance", {}).get("labelAuthority") != "human_adjudicated":
            raise ValueError("non-reviewed corpus row reached encoder training")
        if not isinstance(row.get("modelInput", {}).get("sourceText"), str):
            raise ValueError(f"train row has no source text: {row.get('artifactId')}")
    return sorted(train, key=lambda row: row["artifactId"])


def _validate_train_source_bindings(
        rows: list[dict[str, Any]], refactoring_map: dict[str, Any],
        corpus: dict[str, Any]) -> None:
    files = {
        row["path"]: row for row in refactoring_map.get("files", [])
        if isinstance(row, dict) and isinstance(row.get("path"), str)
    }
    for row in rows:
        artifact = row["artifactId"]
        source = files.get(artifact)
        text = row["modelInput"]["sourceText"]
        if source is None or source.get("contentSha256") != row.get("sourceSha256"):
            raise ValueError(f"training row source hash differs from source map for {artifact}")
        if hashlib.sha256(text.encode("utf-8")).hexdigest() != row.get("sourceSha256"):
            raise ValueError(f"training text digest differs from source fingerprint for {artifact}")
        provenance = row.get("provenance", {})
        if provenance.get("sourceSnapshotSha256") != corpus.get("sourceSnapshotSha256"):
            raise ValueError(f"training row snapshot provenance differs for {artifact}")


def _build_vocab(train_rows: list[dict[str, Any]], max_vocab: int) -> dict[str, int]:
    from collections import Counter

    counts: Counter[str] = Counter()
    for row in train_rows:
        counts.update(_tokenize(row["modelInput"]["sourceText"]))
    specials = [PAD, MASK, UNK, CLS]
    selected = sorted(counts, key=lambda token: (-counts[token], token))[:max_vocab - len(specials)]
    return {token: index for index, token in enumerate(specials + selected)}


def _windows(text: str, vocab: dict[str, int], max_length: int) -> list[list[int]]:
    tokens = _tokenize(text)
    ids = [vocab.get(token, vocab[UNK]) for token in tokens]
    body_size = max_length - 1
    result = []
    for start in range(0, max(1, len(ids)), body_size):
        chunk = ids[start:start + body_size]
        if chunk:
            result.append([vocab[CLS], *chunk])
    return result or [[vocab[CLS]]]


def train_code_transformer(refactoring_map: dict[str, Any], corpus: dict[str, Any],
                           repo_root: Path = ROOT, *, dimension: int = 96,
                           heads: int = 4, layers: int = 2, max_length: int = 192,
                           max_vocab: int = 8192, epochs: int = 8, batch_size: int = 32,
                           learning_rate: float = 3e-4, seed: int = 17,
                           device: str = "auto", position_encoding: str = "learned_absolute") -> tuple[dict[str, Any], dict[str, Any], dict[str, Any]]:
    """Train masked-token denoising on train groups and encode current source.

    Returns (embedding_packet, serializable_model_state, training_report).
    The model state uses tensors encoded as nested JSON lists for portability;
    larger deployments may convert it to safetensors outside this interface.
    """
    try:
        import torch
        from torch import nn
    except ImportError as exc:  # pragma: no cover - environment-specific
        raise RuntimeError("the source Transformer requires PyTorch") from exc

    if refactoring_map.get("schema") != "info_geometry.refactoring_map.v1":
        raise ValueError("unsupported refactoring-map schema")
    snapshot = refactoring_map.get("sourceSnapshot") or {}
    if snapshot.get("worktreeConsistentDuringScan") is not True:
        raise ValueError("refusing an inconsistent refactoring-map snapshot")
    analysis = refactoring_map.get("analysisProvenance") or {}
    if analysis.get("analysisInputsConsistentDuringScan") is not True:
        raise ValueError("refusing inconsistent scanner/Lake provenance")
    if corpus.get("sourceSnapshotSha256") != snapshot.get("pathContentManifestSha256"):
        raise ValueError("corpus and source map refer to different snapshots")
    if corpus.get("scannerSourceSha256") != analysis.get("scannerSourceSha256"):
        raise ValueError("corpus and source map scanner provenance differ")
    if corpus.get("lakeManifestSha256") != analysis.get("lakeManifestSha256"):
        raise ValueError("corpus and source map Lake provenance differ")
    readiness = audit_training_readiness(corpus)
    if not readiness["readyForSupervisedTraining"]:
        raise ValueError(f"reviewed corpus is not ready: {readiness['blockers']}")
    if (dimension < 8 or dimension % heads or heads < 1 or layers < 1
            or max_length < 8 or max_vocab < 8 or epochs < 1 or batch_size < 1
            or not math.isfinite(learning_rate) or learning_rate <= 0):
        raise ValueError("invalid Transformer dimensions or training parameters")
    if position_encoding not in {"learned_absolute", "rotary"}:
        raise ValueError("position_encoding must be learned_absolute or rotary")
    if position_encoding == "rotary" and (dimension // heads) % 2:
        raise ValueError("rotary attention requires an even per-head dimension")
    train_rows = _training_rows(corpus)
    _validate_train_source_bindings(train_rows, refactoring_map, corpus)
    train_artifacts = {row["artifactId"] for row in train_rows}
    vocab = _build_vocab(train_rows, max_vocab)
    sequences = [sequence for row in train_rows
                 for sequence in _windows(row["modelInput"]["sourceText"], vocab, max_length)]
    if not sequences:
        raise ValueError("training source produced no token sequences")

    if device == "auto":
        device = "cuda" if torch.cuda.is_available() else "cpu"
    if device.startswith("cuda") and not torch.cuda.is_available():
        raise ValueError("CUDA was requested but PyTorch reports no available device")
    torch.manual_seed(seed)
    if torch.cuda.is_available():
        torch.cuda.manual_seed_all(seed)
    generator = torch.Generator(device="cpu").manual_seed(seed)

    class RotarySelfAttention(nn.Module):
        def __init__(self) -> None:
            super().__init__()
            self.head_dimension = dimension // heads
            self.qkv = nn.Linear(dimension, 3 * dimension)
            self.output = nn.Linear(dimension, dimension)
            self.attention_dropout = nn.Dropout(0.1)
            self.output_dropout = nn.Dropout(0.1)

        def forward(self, hidden: Any, padding_mask: Any) -> Any:
            batch, sequence, _ = hidden.shape
            qkv = self.qkv(hidden).reshape(batch, sequence, 3, heads, self.head_dimension)
            query, key, value = (qkv[:, :, index].transpose(1, 2) for index in range(3))
            positions = torch.arange(sequence, device=hidden.device, dtype=hidden.dtype)
            query = _apply_rotary_position_encoding(query, positions)
            key = _apply_rotary_position_encoding(key, positions)
            scores = (query @ key.transpose(-2, -1)) / math.sqrt(self.head_dimension)
            scores = scores.masked_fill(padding_mask[:, None, None, :], float("-inf"))
            weights = self.attention_dropout(torch.softmax(scores, dim=-1))
            attended = (weights @ value).transpose(1, 2).reshape(batch, sequence, dimension)
            return self.output_dropout(self.output(attended))

    class RotaryEncoderLayer(nn.Module):
        def __init__(self) -> None:
            super().__init__()
            self.norm1 = nn.LayerNorm(dimension)
            self.attention = RotarySelfAttention()
            self.norm2 = nn.LayerNorm(dimension)
            self.feed_forward = nn.Sequential(
                nn.Linear(dimension, dimension * 4), nn.GELU(), nn.Dropout(0.1),
                nn.Linear(dimension * 4, dimension), nn.Dropout(0.1),
            )

        def forward(self, hidden: Any, padding_mask: Any) -> Any:
            hidden = hidden + self.attention(self.norm1(hidden), padding_mask)
            return hidden + self.feed_forward(self.norm2(hidden))

    class DenoisingEncoder(nn.Module):
        def __init__(self) -> None:
            super().__init__()
            self.token = nn.Embedding(len(vocab), dimension, padding_idx=vocab[PAD])
            if position_encoding == "learned_absolute":
                self.position = nn.Embedding(max_length, dimension)
                layer = nn.TransformerEncoderLayer(
                    d_model=dimension, nhead=heads, dim_feedforward=dimension * 4,
                    dropout=0.1, batch_first=True, norm_first=True,
                )
                self.encoder = nn.TransformerEncoder(layer, num_layers=layers,
                                                     enable_nested_tensor=False)
                self.rotary_layers = None
            else:
                self.position = None
                self.encoder = None
                self.rotary_layers = nn.ModuleList(RotaryEncoderLayer() for _ in range(layers))
            self.norm = nn.LayerNorm(dimension)
            self.decoder = nn.Linear(dimension, len(vocab), bias=False)
            self.decoder.weight = self.token.weight

        def forward(self, ids: Any, padding_mask: Any) -> tuple[Any, Any]:
            hidden = self.token(ids)
            if self.position is not None:
                positions = torch.arange(ids.shape[1], device=ids.device).unsqueeze(0)
                hidden = hidden + self.position(positions)
                encoded = self.encoder(hidden, src_key_padding_mask=padding_mask)
            else:
                for layer in self.rotary_layers:
                    hidden = layer(hidden, padding_mask)
                encoded = hidden
            encoded = self.norm(encoded)
            return encoded[:, 0], self.decoder(encoded)

    model = DenoisingEncoder().to(device)
    optimizer = torch.optim.AdamW(model.parameters(), lr=learning_rate, weight_decay=0.01)
    mask_id, pad_id = vocab[MASK], vocab[PAD]
    epoch_losses: list[float] = []
    for _epoch in range(epochs):
        model.train()
        order = torch.randperm(len(sequences), generator=generator).tolist()
        loss_total = 0.0
        masked_total = 0
        for offset in range(0, len(order), batch_size):
            batch_seq = [sequences[i] for i in order[offset:offset + batch_size]]
            width = max(map(len, batch_seq))
            clean = torch.full((len(batch_seq), width), pad_id, dtype=torch.long)
            for index, sequence in enumerate(batch_seq):
                clean[index, :len(sequence)] = torch.tensor(sequence, dtype=torch.long)
            clean = clean.to(device)
            valid = clean.ne(pad_id)
            eligible = valid.clone()
            eligible[:, 0] = False
            select = torch.rand(clean.shape, generator=generator).to(device) < 0.15
            selected = eligible & select
            # Ensure each nontrivial sequence contributes a prediction target.
            for row_index in range(len(batch_seq)):
                candidates = torch.nonzero(eligible[row_index], as_tuple=False).flatten()
                if candidates.numel() and not selected[row_index].any():
                    selected[row_index, candidates[0]] = True
            if not selected.any():
                continue
            corrupted = clean.clone()
            corrupted[selected] = mask_id
            optimizer.zero_grad(set_to_none=True)
            _pooled, logits = model(corrupted, ~valid)
            loss = nn.functional.cross_entropy(logits[selected], clean[selected])
            loss.backward()
            nn.utils.clip_grad_norm_(model.parameters(), 1.0)
            optimizer.step()
            loss_total += float(loss.detach()) * int(selected.sum())
            masked_total += int(selected.sum())
        if not masked_total:
            raise ValueError("no maskable source tokens in training split")
        epoch_losses.append(loss_total / masked_total)

    model.eval()
    root = repo_root.resolve()
    vectors = []
    with torch.no_grad():
        for row in sorted(refactoring_map.get("files", []), key=lambda item: item.get("path", "")):
            artifact = row.get("path") if isinstance(row, dict) else None
            if not isinstance(artifact, str) or Path(artifact).suffix.lower() not in SOURCE_SUFFIXES:
                continue
            if not isinstance(row.get("contentSha256"), str):
                continue
            path = (root / artifact).resolve()
            try:
                path.relative_to(root)
            except ValueError as exc:
                raise ValueError(f"source path escapes repository: {artifact}") from exc
            if not path.is_file() or _sha256(path) != row["contentSha256"]:
                raise ValueError(f"current source hash differs from map for {artifact}")
            try:
                text = path.read_text(encoding="utf-8")
            except UnicodeDecodeError:
                continue
            pieces = _windows(text, vocab, max_length)
            chunk_vectors = []
            for piece in pieces:
                ids = torch.tensor([piece], dtype=torch.long, device=device)
                padding = torch.zeros_like(ids, dtype=torch.bool)
                pooled, _ = model(ids, padding)
                chunk_vectors.append(pooled[0])
            vector = torch.stack(chunk_vectors).mean(0).float().cpu().tolist()
            vectors.append({"artifactId": artifact, "sourceSha256": row["contentSha256"],
                            "vector": vector})
    if not vectors:
        raise ValueError("source map contains no readable code artifacts")

    train_group_digest = _train_group_digest(corpus["rows"])
    provenance = {
        "method": f"{MODEL_VERSION}.{position_encoding}",
        "dataScope": "repository_train_split",
        "sourceSnapshotSha256": corpus["sourceSnapshotSha256"],
        "trainingSplitGroupsSha256": train_group_digest,
        "trainingArtifactIdsSha256": hashlib.sha256(
            "\0".join(sorted(train_artifacts)).encode("utf-8")).hexdigest(),
    }
    packet = build_encoder_embedding_packet(
        refactoring_map, provenance["method"], vectors, encoder_training=provenance,
    )
    state = {
        "schema": "info_geometry.source_transformer_checkpoint.v1",
        "modelVersion": provenance["method"],
        "config": {"dimension": dimension, "heads": heads, "layers": layers,
                   "maxLength": max_length, "vocabularySize": len(vocab),
                   "positionEncoding": position_encoding,
                   "attentionDirection": "bidirectional",
                   "padId": vocab[PAD], "maskId": vocab[MASK],
                   "unknownId": vocab[UNK], "classId": vocab[CLS]},
        "vocabulary": sorted(vocab.items(), key=lambda item: item[1]),
        "stateDict": {key: tensor.detach().cpu().tolist()
                      for key, tensor in model.state_dict().items()},
        "trainingProvenance": provenance,
    }
    report = {
        "schema": "info_geometry.source_transformer_training_report.v1",
        "modelVersion": provenance["method"],
        "sourceSnapshotSha256": corpus["sourceSnapshotSha256"],
        "corpusRowsSha256": corpus["corpusRowsSha256"],
        "trainingArtifactCount": len(train_artifacts),
        "trainingGroupCount": len({row["splitGroup"] for row in train_rows}),
        "trainingSequenceCount": len(sequences),
        "vocabularySize": len(vocab),
        "epochMaskedTokenLoss": epoch_losses,
        "trainingDataScope": "train_split_source_only_no_labels_or_heldout_source",
        "device": str(device),
        "positionEncoding": position_encoding,
        "attentionDirection": "bidirectional",
        "seed": seed,
        "embeddingPacketSha256": packet["packetSha256"],
        "embeddedArtifactCount": len(vectors),
        "trainingArtifactIdsSha256": provenance["trainingArtifactIdsSha256"],
        "authority": "self-supervised encoder representation; not taxonomy labels or semantic proof",
    }
    return packet, state, report


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("refactoring_map", type=Path)
    parser.add_argument("reviewed_corpus_manifest", type=Path)
    parser.add_argument("--repo-root", type=Path, default=ROOT)
    parser.add_argument("--dimension", type=int, default=96)
    parser.add_argument("--heads", type=int, default=4)
    parser.add_argument("--layers", type=int, default=2)
    parser.add_argument("--max-length", type=int, default=192)
    parser.add_argument("--max-vocab", type=int, default=8192)
    parser.add_argument("--epochs", type=int, default=8)
    parser.add_argument("--batch-size", type=int, default=32)
    parser.add_argument("--learning-rate", type=float, default=3e-4)
    parser.add_argument("--seed", type=int, default=17)
    parser.add_argument("--device", default="auto", help="auto, cpu, or cuda[:index]")
    parser.add_argument("--position-encoding", choices=("learned_absolute", "rotary"),
                        default="learned_absolute")
    parser.add_argument("--embeddings-out", type=Path, required=True)
    parser.add_argument("--checkpoint-out", type=Path, required=True)
    parser.add_argument("--report-out", type=Path, required=True)
    args = parser.parse_args()
    packet, checkpoint, report = train_code_transformer(
        _read_json(args.refactoring_map), _read_json(args.reviewed_corpus_manifest),
        args.repo_root, dimension=args.dimension, heads=args.heads, layers=args.layers,
        max_length=args.max_length, max_vocab=args.max_vocab, epochs=args.epochs,
        batch_size=args.batch_size, learning_rate=args.learning_rate, seed=args.seed,
        device=args.device, position_encoding=args.position_encoding,
    )
    for path, payload in ((args.embeddings_out, packet),
                          (args.checkpoint_out, checkpoint), (args.report_out, report)):
        _write_json(path, payload)
    print(json.dumps({"embeddingPacketSha256": packet["packetSha256"],
                      "embeddedArtifactCount": len(packet["embeddings"]),
                      "finalMaskedTokenLoss": report["epochMaskedTokenLoss"][-1],
                      "device": report["device"]}, sort_keys=True))
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
