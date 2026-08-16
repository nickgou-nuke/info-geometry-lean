#!/usr/bin/env python3
"""Materialize deterministic logic vectors from exact Lean graph overlays.

This is not a training step.  It builds an auditable sparse feature row per
declaration from RDF/de-Bruijn/wire/SCC artifacts, then projects that row through
a deterministic feature hash into a dense vector for retrieval.

Inputs are optional by layer:

* wire topology overlay:
  - ``ig_decl_topologies.jsonl``
  - ``ig_hashes.jsonl``
  - ``ig_logic_tokens.jsonl``
  - ``ig_scc.jsonl``
* RDF / de Bruijn incidence sidecars:
  - ``ig_triples.jsonl``
  - ``ig_binder_incidence.jsonl``

Outputs:

* ``ig_logic_vectors.jsonl``   -- exact features plus deterministic vector
* ``ig_text_index_docs.jsonl`` -- retrieval documents carrying the same vector

Vectors suggest neighborhoods only.  Exact hashes/triples remain the evidence.
"""

from __future__ import annotations

import argparse
import hashlib
import json
import math
import sys
from collections import Counter, defaultdict
from datetime import datetime, timezone
from pathlib import Path
from typing import Any, Iterable

ROOT = Path(__file__).resolve().parents[2]
_SRC = ROOT / "src"
if str(_SRC) not in sys.path:
    sys.path.insert(0, str(_SRC))
if str(ROOT) not in sys.path:
    sys.path.insert(0, str(ROOT))

from igf.common.json_io import iter_jsonl, write_jsonl
from igf.common.time_utils import utc_now_iso


DEFAULT_WIRE_DIR = Path("artifacts/expr-graph/wire-topology")
DEFAULT_RDF_DIR = Path("reports/dag")
DEFAULT_OUTPUT_DIR = Path("artifacts/expr-graph/logic-vectors")


# [lossless-compact] stable_hash folded into igf.common.hashing.stable_hash
from igf.common.hashing import stable_hash


def stable_key(prefix: str, *parts: Any) -> str:
    payload = "|".join(str(part) for part in parts)
    return prefix + "_" + hashlib.sha256(payload.encode("utf-8")).hexdigest()[:32]


def add_feature(features: dict[str, Counter[str]], decl: str, feature: str, weight: float = 1.0) -> None:
    if not decl or not feature:
        return
    features[decl][feature] += weight


def hashed_index(feature: str, dimension: int) -> int:
    digest = hashlib.sha256(feature.encode("utf-8")).digest()
    return int.from_bytes(digest[:8], "big") % dimension


def hashed_sign(feature: str) -> float:
    digest = hashlib.sha256(("sign|" + feature).encode("utf-8")).digest()
    return 1.0 if digest[0] % 2 == 0 else -1.0


def dense_vector(feature_counts: Counter[str], dimension: int) -> tuple[list[float], list[dict[str, Any]]]:
    values = [0.0 for _ in range(dimension)]
    sparse: dict[int, float] = defaultdict(float)
    for feature, count in feature_counts.items():
        idx = hashed_index(feature, dimension)
        value = float(count) * hashed_sign(feature)
        values[idx] += value
        sparse[idx] += value

    norm = math.sqrt(sum(value * value for value in values))
    if norm:
        values = [round(value / norm, 8) for value in values]
        sparse = {idx: value / norm for idx, value in sparse.items()}

    sparse_rows = [
        {"idx": idx, "value": round(value, 8)}
        for idx, value in sorted(sparse.items())
        if value != 0.0
    ]
    return values, sparse_rows


def materialize(
    wire_dir: Path,
    rdf_dir: Path,
    output_dir: Path,
    *,
    dimension: int,
) -> dict[str, Any]:
    features: dict[str, Counter[str]] = defaultdict(Counter)
    modules: dict[str, str] = {}
    identities: dict[str, dict[str, str]] = defaultdict(dict)
    triple_counts: dict[str, int] = defaultdict(int)
    scc_counts: dict[str, int] = defaultdict(int)

    for row in iter_jsonl(wire_dir / "ig_decl_topologies.jsonl"):
        decl = str(row.get("decl", "") or "")
        if not decl:
            continue
        modules.setdefault(decl, str(row.get("module", "") or ""))
        for hash_kind in ["ownerAwareHash", "patternHash", "roleHash"]:
            hash_value = str(row.get(hash_kind, "") or "")
            if hash_value:
                identities[decl][hash_kind] = hash_value
                add_feature(features, decl, f"{hash_kind}:{hash_value}")
            for token in row.get(hash_kind + "Tokens", []) or []:
                add_feature(features, decl, f"{hash_kind}.token:{token}")

    for row in iter_jsonl(wire_dir / "ig_hashes.jsonl"):
        decl = str(row.get("decl", "") or "")
        hash_kind = str(row.get("hashKind", "") or "")
        hash_value = str(row.get("hash", "") or "")
        if decl and hash_kind and hash_value:
            modules.setdefault(decl, str(row.get("module", "") or ""))
            add_feature(features, decl, f"hash:{hash_kind}:{hash_value}")

    for row in iter_jsonl(wire_dir / "ig_logic_tokens.jsonl"):
        decl = str(row.get("decl", "") or "")
        token = str(row.get("value", "") or "")
        hash_kind = str(row.get("hashKind", "") or "")
        multiplicity = float(row.get("multiplicity", 1) or 1)
        if decl and token:
            modules.setdefault(decl, str(row.get("module", "") or ""))
            add_feature(features, decl, f"logicToken:{token}", multiplicity)
            if hash_kind:
                add_feature(features, decl, f"logicTokenKind:{hash_kind}:{token}", multiplicity)

    for row in iter_jsonl(wire_dir / "ig_scc.jsonl"):
        scc_hash = str(row.get("sccPatternHash", "") or "")
        if not scc_hash:
            continue
        for decl in row.get("decls", []) or []:
            decl_text = str(decl or "")
            if not decl_text:
                continue
            scc_counts[decl_text] += 1
            add_feature(features, decl_text, f"sccPatternHash:{scc_hash}")
            for gate_class in row.get("dominantGateClasses", []) or []:
                add_feature(features, decl_text, f"sccGateClass:{gate_class}")

    for row in iter_jsonl(rdf_dir / "ig_triples.jsonl"):
        decl = str(row.get("decl", "") or "")
        if not decl:
            continue
        triple_counts[decl] += 1
        kind = str(row.get("kind", "") or "")
        predicate = str(row.get("predicate", "") or "")
        incidence_hash = str(row.get("incidenceHash", "") or "")
        if kind:
            add_feature(features, decl, f"rdf.kind:{kind}")
        if predicate:
            add_feature(features, decl, f"rdf.predicate:{predicate}")
        if incidence_hash:
            add_feature(features, decl, f"incidenceHash:{incidence_hash}")

    for row in iter_jsonl(rdf_dir / "ig_binder_incidence.jsonl"):
        decl = str(row.get("decl", "") or "")
        binder_hash = str(row.get("binderIncidenceHash", "") or "")
        if not decl:
            continue
        if binder_hash:
            add_feature(features, decl, f"binderIncidenceHash:{binder_hash}")
        add_feature(features, decl, f"binder.boundCount:{row.get('bound_bvar_count', 0)}")
        binder_tag = str(row.get("binder_expr_tag", "") or "")
        if binder_tag:
            add_feature(features, decl, f"binder.exprTag:{binder_tag}")

    logic_rows: list[dict[str, Any]] = []
    text_rows: list[dict[str, Any]] = []
    for decl in sorted(features):
        feature_counts = Counter({feature: count for feature, count in features[decl].items() if count})
        vector, sparse = dense_vector(feature_counts, dimension)
        feature_hash = stable_hash(json.dumps(sorted(feature_counts.items()), sort_keys=True))
        row = {
            "_key": stable_key("lv", decl),
            "kind": "logicVector",
            "decl": decl,
            "module": modules.get(decl, ""),
            "dimension": dimension,
            "featureCount": len(feature_counts),
            "featureHash": feature_hash,
            "features": dict(sorted(feature_counts.items())),
            "sparseVector": sparse,
            "logicVector": vector,
            "identity": dict(sorted(identities.get(decl, {}).items())),
            "tripleCount": triple_counts.get(decl, 0),
            "sccCount": scc_counts.get(decl, 0),
            "truthBoundary": "derived vector shadow; exact evidence remains RDF/deBruijn/wire graph",
        }
        logic_rows.append(row)
        text_rows.append(
            {
                "_key": stable_key("doc", decl),
                "kind": "logicVectorRetrievalDoc",
                "decl": decl,
                "module": modules.get(decl, ""),
                "text": decl,
                "logicVector": vector,
                "featureHash": feature_hash,
                "ownerAwareHash": identities.get(decl, {}).get("ownerAwareHash", ""),
                "patternHash": identities.get(decl, {}).get("patternHash", ""),
                "roleHash": identities.get(decl, {}).get("roleHash", ""),
                "reviewOnly": True,
            }
        )

    counts = {
        "ig_logic_vectors": write_jsonl(output_dir / "ig_logic_vectors.jsonl", logic_rows),
        "ig_text_index_docs": write_jsonl(output_dir / "ig_text_index_docs.jsonl", text_rows),
    }
    metadata = {
        "schema": "info_geometry.logic_vectors.v1",
        "generated_at": utc_now_iso(),
        "wire_dir": str(wire_dir),
        "rdf_dir": str(rdf_dir),
        "output_dir": str(output_dir),
        "dimension": dimension,
        "counts": counts,
        "truth_boundary": "vectors are retrieval shadows; exact graph/hash evidence remains authoritative",
    }
    output_dir.mkdir(parents=True, exist_ok=True)
    (output_dir / "metadata.json").write_text(json.dumps(metadata, indent=2, sort_keys=True) + "\n", encoding="utf-8")
    return metadata


def parse_args() -> argparse.Namespace:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--wire-dir", type=Path, default=DEFAULT_WIRE_DIR)
    parser.add_argument("--rdf-dir", type=Path, default=DEFAULT_RDF_DIR)
    parser.add_argument("--output-dir", type=Path, default=DEFAULT_OUTPUT_DIR)
    parser.add_argument("--dimension", type=int, default=512)
    return parser.parse_args()


def main() -> int:
    args = parse_args()
    if args.dimension <= 0:
        raise SystemExit("--dimension must be positive")
    metadata = materialize(args.wire_dir, args.rdf_dir, args.output_dir, dimension=int(args.dimension))
    print(json.dumps(metadata, indent=2, sort_keys=True))
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
