"""Source-bound, bounded context transport using the existing Sinkhorn owner.

Coupling entries are learned/derived affinities, never dependency witnesses.
This adapter supplies numerical routing weights, not Clifford experts or a
plabic embedding. It does not materialize a whole-repository dense matrix.
"""
from __future__ import annotations

import math
import argparse
from pathlib import Path
from typing import Any

from tools.repository_evolution.latent_taxonomy import build_encoder_embedding_packet


def build_context_transport(
    refactoring_map: dict[str, Any], source_packet: dict[str, Any],
    artifact_ids: list[str], *, temperature: float = 1.0,
    iterations: int = 100, tolerance: float = 1e-10,
    max_context_size: int = 256,
) -> dict[str, Any]:
    """Balance cosine scores on an explicitly selected current-source context.

    Returns JSON-compatible weights P and the classical joint distribution
    P/n with both residuals. Neither matrix is asserted to be a quantum
    density operator. Rows and columns use the same explicit artifact order.
    """
    if (not isinstance(max_context_size, int) or isinstance(max_context_size, bool)
            or max_context_size < 1):
        raise ValueError("max_context_size must be a positive integer")
    if (not isinstance(artifact_ids, list) or not artifact_ids
            or len(artifact_ids) > max_context_size):
        raise ValueError("context must be nonempty and within max_context_size")
    if any(not isinstance(path, str) or not path for path in artifact_ids):
        raise ValueError("artifact IDs must be nonempty strings")
    if len(set(artifact_ids)) != len(artifact_ids):
        raise ValueError("context contains duplicate artifact IDs")
    if not math.isfinite(temperature) or temperature <= 0:
        raise ValueError("temperature must be finite and positive")
    if refactoring_map.get("sourceSnapshot", {}).get("worktreeConsistentDuringScan") is not True:
        raise ValueError("source snapshot was inconsistent during scan")
    if refactoring_map.get("analysisProvenance", {}).get("analysisInputsConsistentDuringScan") is not True:
        raise ValueError("analysis inputs were inconsistent during scan")
    rebuilt = build_encoder_embedding_packet(
        refactoring_map, source_packet.get("encoderVersion"),
        source_packet.get("embeddings"),
        encoder_training=source_packet.get("encoderTraining"),
    )
    if rebuilt != source_packet:
        raise ValueError("source embedding packet is stale, malformed, or has a bad digest")
    rows = {row["artifactId"]: row for row in source_packet["embeddings"]}
    if any(path not in rows for path in artifact_ids):
        raise ValueError("context artifact is absent from the embedding packet")

    import torch
    from tools.shape_sinkhorn_detector import differentiable_sinkhorn_core_decomposition

    values = torch.tensor([rows[path]["vector"] for path in artifact_ids], dtype=torch.float64)
    # Scale first to avoid overflow when normalizing finite, large embeddings.
    magnitude = values.abs().amax(dim=-1, keepdim=True)
    if bool((magnitude == 0).any()):
        raise ValueError("zero source embeddings have no cosine context affinity")
    unit = torch.nn.functional.normalize(values / magnitude, dim=-1)
    logits = (unit @ unit.T) / temperature
    with torch.no_grad():
        _, coupling, _, _, diagnostics = differentiable_sinkhorn_core_decomposition(
            logits, iterations, tolerance=tolerance,
        )
    if not bool(diagnostics["sinkhorn_converged"]):
        raise ValueError("context transport did not converge within the balance tolerance")
    return {
        "schema": "info_geometry.context_transport.v1",
        "sourceSnapshotSha256": source_packet["sourceSnapshotSha256"],
        "sourceEmbeddingPacketSha256": source_packet["packetSha256"],
        "artifactIds": list(artifact_ids),
        "sourceHashes": [rows[path]["sourceSha256"] for path in artifact_ids],
        "scoreMethod": "source_embedding_cosine",
        "temperature": temperature,
        "iterations": iterations,
        "balanceTolerance": tolerance,
        "rowResidual": float(diagnostics["row_error"]),
        "columnResidual": float(diagnostics["column_error"]),
        "coupling": coupling.tolist(),
        "jointDistribution": (coupling / len(artifact_ids)).tolist(),
        "authority": "context_affinity_only_not_dependency_or_taxonomy_evidence",
    }


def main() -> int:
    """Export a bounded coupling from the same packets used by taxonomy fitting."""
    from tools.repository_evolution.edge_attention_baseline import (
        _read_json, _verify_live_sources,
    )
    from tools.repository_evolution.train_graph_context_encoder import _write_json

    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("refactoring_map", type=Path)
    parser.add_argument("embedding_packet", type=Path)
    parser.add_argument("--artifact", action="append", required=True,
                        help="Context artifact ID; repeat in desired matrix order")
    parser.add_argument("--repo-root", type=Path, default=Path.cwd())
    parser.add_argument("--temperature", type=float, default=1.0)
    parser.add_argument("--iterations", type=int, default=100)
    parser.add_argument("--tolerance", type=float, default=1e-10)
    parser.add_argument("--max-context-size", type=int, default=256)
    parser.add_argument("--out", type=Path, required=True)
    args = parser.parse_args()
    source_map = _read_json(args.refactoring_map)
    protected = {args.refactoring_map.resolve(), args.embedding_packet.resolve()}
    protected.update((args.repo_root / row["path"]).resolve()
                     for row in source_map.get("files", []) if "path" in row)
    if args.out.resolve() in protected:
        parser.error("output must not overwrite inputs or scanned source artifacts")
    _verify_live_sources(source_map, set(args.artifact), args.repo_root)
    packet = build_context_transport(
        source_map, _read_json(args.embedding_packet), args.artifact,
        temperature=args.temperature, iterations=args.iterations,
        tolerance=args.tolerance, max_context_size=args.max_context_size,
    )
    _write_json(args.out, packet)
    print(f"Exported {len(args.artifact)}-artifact context to {args.out}")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
