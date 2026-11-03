#!/usr/bin/env python3
"""Verify that the Lean finite cycle witness matches cycle 0 in the archive.

This checks data provenance and transcription only.  Lean remains the proof
authority for the algebraic and Hodge theorems in FiniteDirectedGraphHodge.
"""

from __future__ import annotations

import gzip
import hashlib
import json
import re
from pathlib import Path


ROOT = Path(__file__).resolve().parents[2]
ARCHIVE = ROOT / "artifacts/repository_evolution/commit_topology_20261030"
LEAN_FILE = ROOT / "lean/InfoGeometry/Graph/FiniteDirectedGraphHodge.lean"


def sha256(data: bytes) -> str:
    return hashlib.sha256(data).hexdigest()


def ref_literal(source: str, name: str) -> tuple[str, int]:
    match = re.search(
        rf"def {re.escape(name)} : RankedCommitRef :=\s*"
        rf"⟨\"([0-9a-f]{{40}})\",\s*(\d+)⟩",
        source,
    )
    if match is None:
        raise ValueError(f"could not read Lean reference {name}")
    return match.group(1), int(match.group(2))


def parent_record(source: str, name: str) -> tuple[str, list[str]]:
    match = re.search(
        rf"def {re.escape(name)} : OrderedCommitParents :=\s*"
        rf"⟨(archiveCycle[A-Za-z]+Ref),\s*#\[([^]]*)\]\s*⟩",
        source,
    )
    if match is None:
        raise ValueError(f"could not read Lean parent record {name}")
    parents = re.findall(r"archiveCycle[A-Za-z]+Ref", match.group(2))
    return match.group(1), parents


def local_links(source: str) -> list[tuple[str, str, int]]:
    records = {
        "archiveCycleLeftParents": parent_record(source, "archiveCycleLeftParents"),
        "archiveCycleMiddleParents": parent_record(source, "archiveCycleMiddleParents"),
        "archiveCycleMergeParents": parent_record(source, "archiveCycleMergeParents"),
    }
    block = re.search(
        r"def archiveCycleLink : Fin 4 → ExportedParentLink\s*(.*?)\n\n",
        source,
        re.S,
    )
    if block is None:
        raise ValueError("could not read Lean archiveCycleLink definition")

    links: list[tuple[str, str, int] | None] = [None] * 4
    for index, record_name, slot in re.findall(
        r"\|\s*(\d+)\s*=>\s*orderedParentLinkAt\s+"
        r"(archiveCycle[A-Za-z]+Parents)\s+⟨(\d+),\s*by decide⟩",
        block.group(1),
    ):
        i, parent_slot = int(index), int(slot)
        if i >= len(links) or record_name not in records:
            raise ValueError("invalid Lean archiveCycleLink case")
        child_ref, parents = records[record_name]
        if parent_slot >= len(parents):
            raise ValueError("Lean parent slot is out of bounds")
        links[i] = (parents[parent_slot], child_ref, parent_slot)
    if any(link is None for link in links):
        raise ValueError("Lean archiveCycleLink is missing a Fin 4 case")
    return [link for link in links if link is not None]


def lean_flow(source: str) -> list[int]:
    block = re.search(
        r"def archiveCycleFlow : Fin 4 → ℝ\s*(.*?)\n\n",
        source,
        re.S,
    )
    if block is None:
        raise ValueError("could not read Lean archiveCycleFlow definition")
    values: dict[int, int] = {}
    for index, value in re.findall(r"\|\s*(\d+)\s*=>\s*(-?\d+)", block.group(1)):
        values[int(index)] = int(value)
    if values != {0: 1, 1: 1, 2: -1, 3: 1}:
        raise ValueError(f"unexpected Lean cycle coefficients: {values}")
    return [values[i] for i in range(4)]


def verify() -> dict[str, object]:
    manifest = json.loads((ARCHIVE / "manifest.json").read_text(encoding="utf-8"))
    payloads: dict[str, tuple[bytes, bytes]] = {}
    for name, metadata in manifest["files"].items():
        compressed = (ARCHIVE / name).read_bytes()
        raw = gzip.decompress(compressed)
        if sha256(compressed) != metadata["sha256"]:
            raise ValueError(f"compressed checksum mismatch: {name}")
        if sha256(raw) != metadata["uncompressedSha256"]:
            raise ValueError(f"uncompressed checksum mismatch: {name}")
        payloads[name] = (compressed, raw)

    commits = json.loads(payloads["commits.json.gz"][1])
    cycles = json.loads(payloads["cycles.json.gz"][1])
    cycle = cycles["cycles"][0]
    if cycles["source_sha256"] != manifest["files"]["commits.json.gz"]["uncompressedSha256"]:
        raise ValueError("cycle archive is bound to a different commit graph")

    lean = LEAN_FILE.read_text(encoding="utf-8")
    refs = {
        name: ref_literal(lean, f"archiveCycle{name}Ref")
        for name in ("Root", "Left", "Middle", "Merge")
    }
    lean_ref_names = {
        f"archiveCycle{name}Ref": commit_hash
        for name, (commit_hash, _rank) in refs.items()
    }
    rank_to_hash = {rank: commit_hash for commit_hash, rank in refs.values()}
    for commit_hash, rank in refs.values():
        if cycles["vertices"][rank] != commit_hash:
            raise ValueError(f"Lean rank {rank} does not identify archived commit {commit_hash}")

    archived_commits = {commit["sha"]: commit for commit in commits["commits"]}
    for record_name in (
        "archiveCycleLeftParents",
        "archiveCycleMiddleParents",
        "archiveCycleMergeParents",
    ):
        child_alias, parent_aliases = parent_record(lean, record_name)
        child_hash = lean_ref_names[child_alias]
        parent_hashes = [lean_ref_names[parent] for parent in parent_aliases]
        if archived_commits[child_hash]["parents"] != parent_hashes:
            raise ValueError(f"Lean parent record differs from archived Git parents: {record_name}")

    archive_edges = cycles["edges"]
    if len(commits["commits"]) != len(cycles["vertices"]):
        raise ValueError("commit and cycle archives disagree on vertex count")
    for edge_index, (source_rank, target_rank, parent_slot) in enumerate(archive_edges):
        if not (0 <= source_rank < len(cycles["vertices"])):
            raise ValueError(f"edge {edge_index} has an invalid source rank")
        if not (0 <= target_rank < len(cycles["vertices"])):
            raise ValueError(f"edge {edge_index} has an invalid target rank")
        child_hash = cycles["vertices"][target_rank]
        parent_hash = cycles["vertices"][source_rank]
        parents = archived_commits[child_hash]["parents"]
        if parent_slot >= len(parents) or parents[parent_slot] != parent_hash:
            raise ValueError(f"cycle edge {edge_index} disagrees with raw Git parents")

    # Compute connected components from the archived edge endpoints instead
    # of trusting the component count copied into the manifest.
    parent = list(range(len(cycles["vertices"])))

    def find(vertex: int) -> int:
        while parent[vertex] != vertex:
            parent[vertex] = parent[parent[vertex]]
            vertex = parent[vertex]
        return vertex

    for source_rank, target_rank, _parent_slot in archive_edges:
        source_root, target_root = find(source_rank), find(target_rank)
        if source_root != target_root:
            parent[target_root] = source_root
    actual_components = len({find(vertex) for vertex in range(len(parent))})

    archived: dict[tuple[str, str, int], int] = {}
    for edge_index, coefficient in cycle["signed_edges"]:
        source_rank, target_rank, parent_slot = archive_edges[edge_index]
        archived[(rank_to_hash[source_rank], rank_to_hash[target_rank], parent_slot)] = coefficient

    links = [
        (lean_ref_names[src], lean_ref_names[dst], slot)
        for src, dst, slot in local_links(lean)
    ]
    flow = lean_flow(lean)
    transcribed = {link: flow[i] for i, link in enumerate(links)}
    if transcribed != archived:
        raise ValueError(f"Lean witness differs from archive cycle 0: {transcribed} != {archived}")

    # Recheck the oriented incidence boundary directly on commit hashes.
    boundary: dict[str, int] = {}
    for (src, dst, _slot), coefficient in archived.items():
        boundary[src] = boundary.get(src, 0) - coefficient
        boundary[dst] = boundary.get(dst, 0) + coefficient
    if any(boundary.values()):
        raise ValueError(f"archive cycle 0 has nonzero boundary: {boundary}")

    metrics = manifest["metrics"]
    if len(cycles["vertices"]) != metrics["vertices"] or len(archive_edges) != metrics["edges"]:
        raise ValueError("archive cycle graph dimensions disagree with manifest")
    if actual_components != metrics["components"]:
        raise ValueError(
            f"recomputed component count {actual_components} differs from manifest "
            f"count {metrics['components']}"
        )
    all_cycles = cycles["cycles"]
    pivots = [entry["pivot"]["edge_index"] for entry in all_cycles]
    if len(pivots) != len(set(pivots)):
        raise ValueError("archive cycle pivots are not distinct")
    for cycle_index, entry in enumerate(all_cycles):
        coefficients = dict(entry["signed_edges"])
        if len(coefficients) != len(entry["signed_edges"]):
            raise ValueError(f"cycle {cycle_index} repeats an edge")
        if coefficients.get(entry["pivot"]["edge_index"]) != 1:
            raise ValueError(f"cycle {cycle_index} has a non-unit pivot coefficient")

        cycle_boundary: dict[int, int] = {}
        for edge_index, coefficient in coefficients.items():
            source, target, _parent_slot = archive_edges[edge_index]
            cycle_boundary[source] = cycle_boundary.get(source, 0) - coefficient
            cycle_boundary[target] = cycle_boundary.get(target, 0) + coefficient
        if any(cycle_boundary.values()):
            raise ValueError(f"cycle {cycle_index} has nonzero incidence boundary")

        for pivot_index in pivots:
            expected = int(pivot_index == entry["pivot"]["edge_index"])
            if coefficients.get(pivot_index, 0) != expected:
                raise ValueError(f"cycle pivot submatrix is not identity at cycle {cycle_index}")

    cycle_rank = len(archive_edges) - len(cycles["vertices"]) + metrics["components"]
    if len(all_cycles) != metrics["betti1"] or len(all_cycles) != cycle_rank:
        raise ValueError("cycle count does not match the graph's first Betti number")

    return {
        "status": "verified_transcription",
        "archive_cycle_index": cycle["cycle_index"],
        "archive_cycle_edges": len(archived),
        "lean_local_edge_order": len(links),
        "boundary_zero": True,
        "all_archive_cycles_boundary_zero": True,
        "cycle_pivot_submatrix_identity": True,
        "cycle_count_matches_graph_cycle_rank": True,
        "archive_cycle_basis_size": len(all_cycles),
        "archive_vertices": metrics["vertices"],
        "archive_edges": metrics["edges"],
        "recomputed_components": actual_components,
        "archive_betti1": metrics["betti1"],
        "archive_source_sha256": cycles["source_sha256"],
    }


if __name__ == "__main__":
    print(json.dumps(verify(), indent=2, sort_keys=True))
