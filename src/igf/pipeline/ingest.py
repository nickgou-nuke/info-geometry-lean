from __future__ import annotations

from pathlib import Path
from typing import Any

from igf.artifacts.io import read_jsonl
from igf.graph.arango_client import ensure_collections_and_indexes


FILE_TO_COLLECTION = {
    "ig_patch_runs.jsonl": "ig_patch_runs",
    "ig_chiral_patches.jsonl": "ig_chiral_patches",
    "ig_patch_spectral_signatures.jsonl": "ig_patch_spectral_signatures",
    "ig_patch_members.jsonl": "ig_patch_members",
    "ig_patch_edges.jsonl": "ig_patch_edges",
}


def _upsert_document(collection: Any, row: dict[str, Any]) -> None:
    try:
        collection.insert(row, overwrite=True, overwrite_mode="update")
    except TypeError:
        key = row.get("_key")
        if key and collection.has(key):
            collection.update(row)
        else:
            collection.insert(row)


def ingest_artifacts(db: Any, artifact_dir: Path) -> dict[str, Any]:
    ensure_collections_and_indexes(db)
    counts: dict[str, int] = {}

    for file_name, collection_name in FILE_TO_COLLECTION.items():
        path = artifact_dir / file_name
        if not path.exists():
            raise FileNotFoundError(path)

        collection = db.collection(collection_name)
        count = 0
        for row in read_jsonl(path):
            if not row.get("_key") and collection_name not in {"ig_patch_members", "ig_patch_edges"}:
                raise ValueError(f"{path}: vertex row missing _key")
            _upsert_document(collection, row)
            count += 1
        counts[collection_name] = count

    return {"ok": True, "artifact_dir": str(artifact_dir), "ingested": counts}

