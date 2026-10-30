#!/usr/bin/env python3
"""Infer an unrooted structural-affinity tree from observed categorical markers.

This offline, standard-library-only tool never queries Git, ArangoDB, or a URL.
Hashes are categorical allele labels: unequal hashes contribute one mismatch,
regardless of their hexadecimal or bit distance. A tree is descriptive affinity,
not evidence of historical ancestry, theorem equivalence, or a molecular clock.

Primary input: repo-character-profiles/v1 with provenance and taxa, each having
id, optional label, and characters {marker: {state, algorithm_version}}.
Only marker columns observed in every taxon with one shared algorithm version
enter the distance matrix. Missing values are unknown, never an observed allele.

Adapter input: repo-dna-snapshots/v1 with snapshots containing declarations in
the native Lean Indexer shape: name, typeDigest, and optional valueDigest. Digest
objects must have algorithmVersion, a 64-hex digest, and boolean openTerm. Only
closed digests enter the profiles. A null digest is unobserved. Snapshot IDs use
sample_id, generation, commit, then id, in that order. Historical IDs are neither
required nor verified. Exact qualified declaration names are assumed alignments;
there is no automatic rename matching or homology inference.

Usage: python dna_character_tree.py --input profiles.json --out affinity.json
"""

from __future__ import annotations

import argparse
from collections import Counter
from fractions import Fraction
import itertools
import json
import math
from pathlib import Path
import random
import re
import sys
from typing import Any, Iterable, Sequence


PRIMARY_SCHEMA = "repo-character-profiles/v1"
SNAPSHOT_SCHEMA = "repo-dna-snapshots/v1"
OUTPUT_SCHEMA = "repo-structural-affinity/v1"
CLAIM_SCOPE = "unrooted_structural_affinity_not_historical_ancestry"
MAX_TAXA = 128
MAX_QUARTETS = 4096
HEX_DIGEST = re.compile(r"[0-9a-fA-F]{64}\Z")


class InputError(ValueError):
    """Input does not support the requested, explicitly scoped inference."""


def _text(value: Any, where: str) -> str:
    if not isinstance(value, str) or not value.strip():
        raise InputError(f"{where} must be a nonempty string")
    return value


def _object(value: Any, where: str) -> dict[str, Any]:
    if not isinstance(value, dict):
        raise InputError(f"{where} must be an object")
    return value


def _taxon_count(count: int) -> None:
    if count < 3:
        raise InputError("at least three uniquely identified taxa are required")
    if count > MAX_TAXA:
        raise InputError(f"at most {MAX_TAXA} taxa are supported by this offline implementation")


def _snapshot_id(snapshot: dict[str, Any], position: int) -> str:
    for field in ("sample_id", "generation", "commit", "id"):
        if field in snapshot and snapshot[field] is not None:
            return _text(snapshot[field], f"snapshots[{position}].{field}")
    raise InputError(f"snapshots[{position}] needs sample_id, generation, commit, or id")


def _digest_character(value: Any, where: str) -> tuple[dict[str, str] | None, str]:
    if value is None:
        return None, "absent"
    digest = _object(value, where)
    version = _text(digest.get("algorithmVersion"), f"{where}.algorithmVersion")
    state = digest.get("digest")
    if not isinstance(state, str) or HEX_DIGEST.fullmatch(state) is None:
        raise InputError(f"{where}.digest must be exactly 64 hexadecimal characters")
    if not isinstance(digest.get("openTerm"), bool):
        raise InputError(f"{where}.openTerm must explicitly be true or false")
    if "nodeCount" in digest:
        count = digest["nodeCount"]
        if isinstance(count, bool) or not isinstance(count, int) or count < 0:
            raise InputError(f"{where}.nodeCount must be a nonnegative integer")
    if digest["openTerm"]:
        return None, "open"
    return {"state": state.lower(), "algorithm_version": version}, "closed"


def _adapt_snapshots(document: dict[str, Any]) -> tuple[list[dict[str, Any]], set[str], dict[str, Any]]:
    snapshots = document.get("snapshots")
    if not isinstance(snapshots, list):
        raise InputError("snapshots must be an array")
    _taxon_count(len(snapshots))
    taxa: list[dict[str, Any]] = []
    marker_universe: set[str] = set()
    reports: list[dict[str, Any]] = []
    for position, raw_snapshot in enumerate(snapshots):
        snapshot = _object(raw_snapshot, f"snapshots[{position}]")
        taxon_id = _snapshot_id(snapshot, position)
        declarations = snapshot.get("declarations")
        if not isinstance(declarations, list):
            raise InputError(f"snapshot {taxon_id!r}.declarations must be an array")
        characters: dict[str, dict[str, str]] = {}
        names: set[str] = set()
        counts: Counter[str] = Counter()
        skipped: list[dict[str, str]] = []
        for row_number, raw_decl in enumerate(declarations):
            where = f"snapshot {taxon_id!r}.declarations[{row_number}]"
            decl = _object(raw_decl, where)
            provenance = decl.get("provenance", {})
            is_proxy = (
                decl.get("schema") == "hive.packet.expr_fingerprint.v1"
                or (isinstance(provenance, dict) and provenance.get("method") == "metadata_proxy_v1")
            )
            if is_proxy:
                raise InputError(f"{where} is a metadata proxy, not a native term-digest record")
            name = _text(decl.get("name"), f"{where}.name")
            if name in names:
                raise InputError(f"snapshot {taxon_id!r} repeats declaration {name!r}")
            names.add(name)
            if "typeDigest" not in decl:
                raise InputError(f"{where} lacks native typeDigest; names or metadata alone are not DNA")
            for side, field in (("type", "typeDigest"), ("value", "valueDigest")):
                marker = f"{side}:{name}"
                marker_universe.add(marker)
                character, status = _digest_character(decl.get(field), f"{where}.{field}")
                counts[status] += 1
                if character is not None:
                    characters[marker] = character
                else:
                    skipped.append({"marker": marker, "reason": status})
        taxon = {"id": taxon_id, "characters": characters}
        if "label" in snapshot:
            taxon["label"] = _text(snapshot["label"], f"snapshot {taxon_id!r}.label")
        taxa.append(taxon)
        assertions = {key: snapshot[key] for key in ("id", "sample_id", "generation", "commit") if key in snapshot}
        reports.append({
            "taxon_id": taxon_id,
            "source_identifiers_asserted": assertions,
            "declaration_count": len(names),
            "closed_digest_fields": counts["closed"],
            "absent_digest_fields": counts["absent"],
            "open_digest_fields": counts["open"],
            "skipped_digest_fields": skipped,
        })
    return taxa, marker_universe, {
        "method": "native_term_digest_fields",
        "alignment_assumption": "exact qualified declaration names; type and value are separate markers",
        "automatic_rename_or_homology_matching": False,
        "snapshots": sorted(reports, key=lambda row: row["taxon_id"]),
    }


def _prepare_input(document: Any) -> tuple[list[dict[str, Any]], dict[str, Any], set[str], dict[str, Any] | None]:
    document = _object(document, "input")
    provenance = _object(document.get("provenance", {}), "provenance")
    schema = document.get("schema")
    adapter = None
    marker_universe: set[str] = set()
    if schema == SNAPSHOT_SCHEMA:
        raw_taxa, marker_universe, adapter = _adapt_snapshots(document)
    elif schema == PRIMARY_SCHEMA:
        raw_taxa = document.get("taxa")
        if not isinstance(raw_taxa, list):
            raise InputError("taxa must be an array")
    else:
        raise InputError(f"schema must be {PRIMARY_SCHEMA!r} or {SNAPSHOT_SCHEMA!r}")
    _taxon_count(len(raw_taxa))
    taxa: list[dict[str, Any]] = []
    seen: set[str] = set()
    for position, raw in enumerate(raw_taxa):
        row = _object(raw, f"taxa[{position}]")
        taxon_id = _text(row.get("id"), f"taxa[{position}].id")
        if taxon_id in seen:
            raise InputError(f"duplicate taxon id {taxon_id!r}")
        seen.add(taxon_id)
        label = _text(row.get("label", taxon_id), f"taxa[{position}].label")
        characters = _object(row.get("characters"), f"taxa[{position}].characters")
        clean: dict[str, dict[str, str]] = {}
        for marker, raw_character in characters.items():
            _text(marker, f"taxon {taxon_id!r} marker id")
            character = _object(raw_character, f"taxon {taxon_id!r} marker {marker!r}")
            clean[marker] = {
                "state": _text(character.get("state"), f"marker {marker!r}.state"),
                "algorithm_version": _text(character.get("algorithm_version"), f"marker {marker!r}.algorithm_version"),
            }
        marker_universe.update(clean)
        taxa.append({"id": taxon_id, "label": label, "characters": clean})
    return sorted(taxa, key=lambda row: row["id"]), provenance, marker_universe, adapter


def _fraction(value: Any) -> Fraction:
    if isinstance(value, bool) or not isinstance(value, (int, float, Fraction)):
        raise InputError("distance entries must be finite numbers")
    if isinstance(value, float):
        if not math.isfinite(value):
            raise InputError("distance entries must be finite numbers")
        return Fraction(str(value))
    return Fraction(value)


def _validate_distances(taxon_ids: Sequence[str], matrix: Sequence[Sequence[Any]]) -> list[list[Fraction]]:
    _taxon_count(len(taxon_ids))
    if len(set(taxon_ids)) != len(taxon_ids):
        raise InputError("taxon ids must be unique")
    for taxon_id in taxon_ids:
        _text(taxon_id, "taxon id")
    n = len(taxon_ids)
    if len(matrix) != n or any(len(row) != n for row in matrix):
        raise InputError("distance matrix dimensions must match taxa")
    result = [[_fraction(value) for value in row] for row in matrix]
    for i in range(n):
        if result[i][i] != 0:
            raise InputError("distance matrix diagonal must be zero")
        for j in range(i + 1, n):
            if result[i][j] < 0 or result[j][i] != result[i][j]:
                raise InputError("distance matrix must be symmetric and nonnegative")
    return result


def neighbor_joining(taxon_ids: Sequence[str], matrix: Sequence[Sequence[Any]]) -> dict[str, Any]:
    """Deterministic exact-arithmetic NJ; retain, report, and never clip negatives.

    The input matrix may be nonadditive. Returned edge endpoints are undirected;
    internal nodes have no asserted ancestor identity. Lexically ordered taxon IDs
    and then generated node IDs break exact Q ties deterministically.
    """
    values = _validate_distances(taxon_ids, matrix)
    order = sorted(range(len(taxon_ids)), key=lambda i: taxon_ids[i])
    nodes = [{"id": f"leaf:{i}", "kind": "taxon", "taxon_id": taxon_ids[old]} for i, old in enumerate(order)]
    active = [node["id"] for node in nodes]
    distances: dict[tuple[str, str], Fraction] = {}

    def pair(a: str, b: str) -> tuple[str, str]:
        return (a, b) if a < b else (b, a)

    for i, a in enumerate(active):
        for j in range(i + 1, len(active)):
            distances[pair(a, active[j])] = values[order[i]][order[j]]

    def distance(a: str, b: str) -> Fraction:
        return Fraction(0) if a == b else distances[pair(a, b)]

    edges: list[dict[str, Any]] = []
    internal_count = 0

    def internal() -> str:
        nonlocal internal_count
        internal_count += 1
        node_id = f"internal:{internal_count}"
        nodes.append({"id": node_id, "kind": "internal", "interpretation": "inferred grouping; no ancestor asserted"})
        return node_id

    def add_edge(a: str, b: str, length: Fraction) -> None:
        left, right = pair(a, b)
        edges.append({"a": left, "b": right, "length": float(length), "exact_length": str(length)})

    while len(active) > 3:
        active.sort()
        m = len(active)
        sums = {a: sum((distance(a, b) for b in active if b != a), Fraction(0)) for a in active}
        _, a, b = min(
            ((m - 2) * distance(a, b) - sums[a] - sums[b], a, b)
            for a, b in itertools.combinations(active, 2)
        )
        joined = internal()
        dab = distance(a, b)
        limb_a = (dab + (sums[a] - sums[b]) / (m - 2)) / 2
        add_edge(joined, a, limb_a)
        add_edge(joined, b, dab - limb_a)
        remaining = [node for node in active if node not in (a, b)]
        for other in remaining:
            distances[pair(joined, other)] = (distance(a, other) + distance(b, other) - dab) / 2
        active = remaining + [joined]
    a, b, c = sorted(active)
    center = internal()
    add_edge(center, a, (distance(a, b) + distance(a, c) - distance(b, c)) / 2)
    add_edge(center, b, (distance(a, b) + distance(b, c) - distance(a, c)) / 2)
    add_edge(center, c, (distance(a, c) + distance(b, c) - distance(a, b)) / 2)
    edges.sort(key=lambda edge: (edge["a"], edge["b"]))
    negative = [edge for edge in edges if Fraction(edge["exact_length"]) < 0]
    return {
        "method": "neighbor_joining",
        "q_criterion": "(active_count - 2) * d(i,j) - row_sum(i) - row_sum(j)",
        "arithmetic": "exact rational arithmetic",
        "orientation": "unrooted",
        "undirected": True,
        "branch_length_unit": "input distance units; no time interpretation",
        "negative_lengths_clipped": False,
        "negative_branch_count": len(negative),
        "negative_branches": negative,
        "nodes": nodes,
        "edges": edges,
    }


def _unrank_combination(n: int, k: int, rank: int) -> tuple[int, ...]:
    answer: list[int] = []
    start = 0
    for remaining in range(k, 0, -1):
        for value in range(start, n - remaining + 1):
            block = math.comb(n - value - 1, remaining - 1)
            if rank < block:
                answer.append(value)
                start = value + 1
                break
            rank -= block
    return tuple(answer)


def four_point_diagnostic(matrix: Sequence[Sequence[Any]], max_quartets: int = MAX_QUARTETS) -> dict[str, Any]:
    """Largest-minus-second-largest quartet sum; a nonadditivity diagnostic."""
    if max_quartets < 1:
        raise InputError("max_quartets must be positive")
    n = len(matrix)
    values = [[_fraction(value) for value in row] for row in matrix]
    total = math.comb(n, 4) if n >= 4 else 0
    if not total:
        return {"status": "requires_at_least_four_taxa", "total_quartets": 0, "evaluated_quartets": 0}
    quartets: Iterable[tuple[int, ...]]
    if total <= max_quartets:
        quartets = itertools.combinations(range(n), 4)
        scope = "all_quartets"
    else:
        ranks = sorted(random.Random(0).sample(range(total), max_quartets))
        quartets = (_unrank_combination(n, 4, rank) for rank in ranks)
        scope = "deterministic_sample_of_quartets"
    residuals: list[Fraction] = []
    for a, b, c, d in quartets:
        sums = sorted((values[a][b] + values[c][d], values[a][c] + values[b][d], values[a][d] + values[b][c]))
        residuals.append(sums[2] - sums[1])
    evaluated = len(residuals)
    return {
        "status": "measured",
        "evaluation_scope": scope,
        "sampling_seed": 0 if total > max_quartets else None,
        "total_quartets": total,
        "evaluated_quartets": evaluated,
        "residual_definition": "largest minus second-largest of the three paired distance sums",
        "positive_residual_quartets": sum(value > 0 for value in residuals),
        "max_residual": float(max(residuals)),
        "mean_residual": float(sum(residuals, Fraction(0)) / evaluated),
        "rms_residual": math.sqrt(sum(float(value * value) for value in residuals) / evaluated),
        "interpretation": "descriptive tree-additivity diagnostic, not model confidence or ancestry evidence",
    }


def tree_fit_diagnostic(taxon_ids: Sequence[str], matrix: Sequence[Sequence[Any]], tree: dict[str, Any]) -> dict[str, Any]:
    """Compare every observed pair distance with its inferred tree path distance."""
    values = _validate_distances(taxon_ids, matrix)
    adjacent: dict[str, list[tuple[str, Fraction]]] = {node["id"]: [] for node in tree["nodes"]}
    tips = {node["taxon_id"]: node["id"] for node in tree["nodes"] if node["kind"] == "taxon"}
    for edge in tree["edges"]:
        length = Fraction(edge["exact_length"])
        adjacent[edge["a"]].append((edge["b"], length))
        adjacent[edge["b"]].append((edge["a"], length))
    residuals: list[Fraction] = []
    for i, taxon_id in enumerate(taxon_ids):
        paths = {tips[taxon_id]: Fraction(0)}
        pending = [tips[taxon_id]]
        while pending:
            node = pending.pop()
            for neighbor, length in adjacent[node]:
                if neighbor not in paths:
                    paths[neighbor] = paths[node] + length
                    pending.append(neighbor)
        for j in range(i + 1, len(taxon_ids)):
            residuals.append(paths[tips[taxon_ids[j]]] - values[i][j])
    count = len(residuals)
    return {
        "pair_count": count,
        "path_distance_rmse": math.sqrt(sum(float(value * value) for value in residuals) / count),
        "mean_absolute_residual": float(sum((abs(value) for value in residuals), Fraction(0)) / count),
        "max_absolute_residual": float(max(abs(value) for value in residuals)),
        "exact_fit": all(value == 0 for value in residuals),
        "negative_branch_lengths_included": True,
        "interpretation": "descriptive reconstruction error, not model confidence or historical validation",
    }


def infer_tree(document: Any) -> dict[str, Any]:
    taxa, provenance, marker_universe, adapter = _prepare_input(document)
    retained: list[dict[str, Any]] = []
    excluded: list[dict[str, Any]] = []
    reason_counts: Counter[str] = Counter()
    taxon_ids = [taxon["id"] for taxon in taxa]
    for marker in sorted(marker_universe):
        observations = [taxon["characters"].get(marker) for taxon in taxa]
        missing = [taxon["id"] for taxon, observation in zip(taxa, observations) if observation is None]
        versions = sorted({observation["algorithm_version"] for observation in observations if observation is not None})
        reasons = []
        if missing:
            reasons.append("missing_observations")
        if len(versions) > 1:
            reasons.append("algorithm_version_mismatch")
        if reasons:
            reason_counts.update(reasons)
            excluded.append({
                "marker": marker,
                "reasons": reasons,
                "observed_taxa": len(taxa) - len(missing),
                "missing_taxa": missing,
                "observed_algorithm_versions": versions,
            })
        else:
            retained.append({"marker": marker, "algorithm_version": versions[0]})
    if not retained:
        raise InputError(
            "no comparable complete-case marker columns: missing or open observations are unknown, "
            "and algorithm versions must match across all taxa; no zero-distance matrix was inferred"
        )
    marker_ids = [row["marker"] for row in retained]
    patterns = Counter(tuple(taxon["characters"][marker]["state"] for taxon in taxa) for marker in marker_ids)
    profile_groups: dict[tuple[str, ...], list[str]] = {}
    for taxon in taxa:
        profile = tuple(taxon["characters"][marker]["state"] for marker in marker_ids)
        profile_groups.setdefault(profile, []).append(taxon["id"])
    indistinguishable = sorted(group for group in profile_groups.values() if len(group) > 1)
    matrix = [[Fraction(0) for _ in taxa] for _ in taxa]
    for i in range(len(taxa)):
        for j in range(i + 1, len(taxa)):
            mismatches = sum(count for states, count in patterns.items() if states[i] != states[j])
            matrix[i][j] = matrix[j][i] = Fraction(mismatches, len(marker_ids))
    tree = neighbor_joining(taxon_ids, matrix)
    labels = {taxon["id"]: taxon["label"] for taxon in taxa}
    for node in tree["nodes"]:
        if node["kind"] == "taxon":
            node["label"] = labels[node["taxon_id"]]
    tree["branch_length_unit"] = "retained-marker mismatch fraction; no time interpretation"
    return {
        "schema": OUTPUT_SCHEMA,
        "claim_scope": CLAIM_SCOPE,
        "input_schema": document["schema"],
        "provenance": provenance,
        "provenance_status": "input assertions preserved; no external source verification performed",
        "historical_binding": {
            "verified": False,
            "required_for_inference": False,
            "note": "No generation-to-commit mapping was required or verified. Comparison to Git needs a separate mapping.",
        },
        "taxa": [{"id": row["id"], "label": row["label"]} for row in taxa],
        "alignment": {
            "method": "complete-case exact marker IDs with matching per-marker algorithm versions",
            "missing_state_policy": "unknown; exclude the column from all pair comparisons",
            "marker_universe_count": len(marker_universe),
            "retained_marker_count": len(retained),
            "excluded_marker_count": len(excluded),
            "exclusion_reason_counts": dict(sorted(reason_counts.items())),
            "retained_markers": retained,
            "excluded_markers": excluded,
            "per_taxon_observed_marker_counts": {row["id"]: len(row["characters"]) for row in taxa},
        },
        "adapter": adapter,
        "distance_matrix": {
            "taxon_order": taxon_ids,
            "metric": "fraction_of_retained_columns_with_unequal_categorical_states",
            "hash_interpretation": "categorical labels only; no bit, hexadecimal, or numeric hash distance",
            "common_denominator": len(marker_ids),
            "values": [[float(value) for value in row] for row in matrix],
        },
        "tree": tree,
        "diagnostics": {
            "profile_resolution": {
                "scope": "retained_complete_case_markers_only",
                "distinct_profile_count": len(profile_groups),
                "constant_marker_count": sum(count for pattern, count in patterns.items()
                                             if len(set(pattern)) == 1),
                "variable_marker_count": sum(count for pattern, count in patterns.items()
                                             if len(set(pattern)) > 1),
                "indistinguishable_taxon_groups": indistinguishable,
                "all_profiles_identical": len(profile_groups) == 1,
                "interpretation": (
                    "Taxa within each group cannot be distinguished by retained markers; "
                    "tie-broken tree resolution is not evidence of differences or ancestry. "
                    "Distinct profiles alone do not establish a uniquely supported topology."
                ),
            },
            "four_point": four_point_diagnostic(matrix),
            "tree_fit": tree_fit_diagnostic(taxon_ids, matrix, tree),
        },
        "limitations": [
            "Marker identity and comparable versions are input assumptions; homology is not established.",
            "Equal-weight categorical mismatch measures structural affinity, not the number of source edits or mutations.",
            "Identical observed profiles can have distance zero despite unobserved differences.",
            "Complete-case filtering can discard much of the input; coverage is part of the result.",
            "Correlated markers and shared subterms are not independent evolutionary characters.",
            "Tree branches have no ancestor identity, root, dates, or molecular-clock interpretation.",
            "A tree cannot express every merge or shared-structure relationship; residuals describe lost fit.",
            "Negative branch lengths are preserved as a warning about the descriptive tree fit.",
        ],
    }


def main(argv: Sequence[str] | None = None) -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--input", required=True, type=Path)
    parser.add_argument("--out", required=True, type=Path)
    args = parser.parse_args(argv)
    try:
        if args.input.resolve() == args.out.resolve():
            raise InputError("output must not overwrite the input")
        with args.input.open(encoding="utf-8") as handle:
            document = json.load(handle)
        result = infer_tree(document)
        encoded = json.dumps(result, ensure_ascii=False, indent=2, allow_nan=False) + "\n"
        args.out.parent.mkdir(parents=True, exist_ok=True)
        args.out.write_text(encoded, encoding="utf-8")
    except (OSError, UnicodeError, json.JSONDecodeError, InputError) as exc:
        print(f"ERROR: {exc}", file=sys.stderr)
        return 2
    print(json.dumps({
        "out": str(args.out),
        "taxa": len(result["taxa"]),
        "retained_markers": result["alignment"]["retained_marker_count"],
        "excluded_markers": result["alignment"]["excluded_marker_count"],
        "claim_scope": CLAIM_SCOPE,
    }))
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
