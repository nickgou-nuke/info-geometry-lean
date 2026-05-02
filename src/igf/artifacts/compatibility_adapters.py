from __future__ import annotations

import json
from pathlib import Path
from typing import Any

from igf.policy.claim_scope import apply_default_claim_policy


def _load_jsonl(path: Path) -> list[dict[str, Any]]:
    rows: list[dict[str, Any]] = []
    with path.open("r", encoding="utf-8") as f:
        for line in f:
            line = line.strip()
            if not line:
                continue
            rows.append(json.loads(line))
    return rows


def _write_jsonl(path: Path, rows: list[dict[str, Any]]) -> None:
    path.parent.mkdir(parents=True, exist_ok=True)
    with path.open("w", encoding="utf-8") as f:
        for row in rows:
            f.write(json.dumps(row, ensure_ascii=False) + "\n")


def _infer_run_id_from_patch_from(edge_from: str) -> str:
    # ig_chiral_patches/patch_ego_run_1777714851_... -> run_1777714851
    key = edge_from.split("/", 1)[-1]
    marker = "_run_"
    i = key.find(marker)
    if i == -1:
        return ""
    rest = key[i + 1 :]  # starts with run_
    parts = rest.split("_")
    if len(parts) < 2:
        return ""
    return f"{parts[0]}_{parts[1]}"  # run_<ts>


def normalize_artifacts(input_dir: Path, output_dir: Path) -> dict[str, Any]:
    runs = _load_jsonl(input_dir / "ig_patch_runs.jsonl")
    patches = _load_jsonl(input_dir / "ig_chiral_patches.jsonl")
    spectral = _load_jsonl(input_dir / "ig_patch_spectral_signatures.jsonl")
    members = _load_jsonl(input_dir / "ig_patch_members.jsonl")
    edges = _load_jsonl(input_dir / "ig_patch_edges.jsonl")

    patch_by_key: dict[str, dict[str, Any]] = {}
    for p in patches:
        p.setdefault("schema_version", "ig.chiral_patch.v1.2")
        apply_default_claim_policy(p)
        patch_by_key[p.get("_key", "")] = p

    run_by_key: dict[str, dict[str, Any]] = {}
    for r in runs:
        rid = r.get("run_id") or r.get("_key")
        r["run_id"] = rid
        r.setdefault("schema_version", "ig.patch_run.v1")
        r.setdefault("algorithm_version", r.get("patch_algorithm", "unknown"))
        apply_default_claim_policy(r)
        run_by_key[r.get("_key", "")] = r

    for s in spectral:
        s.setdefault("schema_version", "ig.patch_spectral_signature.v1.2")
        apply_default_claim_policy(s)
        pid = s.get("patch_id") or s.get("_key")
        s["patch_id"] = pid
        if not s.get("run_id"):
            p = patch_by_key.get(pid)
            if p and p.get("run_id"):
                s["run_id"] = p["run_id"]
        if not s.get("spectral_status"):
            s["spectral_status"] = "exact" if s.get("eigenvalues") else "trivial"

    for m in members:
        m.setdefault("schema_version", "ig.patch_member.v1")
        from_key = m.get("_from", "").split("/", 1)[-1]
        p = patch_by_key.get(from_key)
        m.setdefault("patch_id", p.get("patch_id") if p else from_key)
        if not m.get("run_id"):
            if p and p.get("run_id"):
                m["run_id"] = p["run_id"]
            else:
                m["run_id"] = _infer_run_id_from_patch_from(m.get("_from", ""))

    for e in edges:
        e.setdefault("schema_version", "ig.patch_edge.v1")
        from_key = e.get("_from", "").split("/", 1)[-1]
        to_key = e.get("_to", "").split("/", 1)[-1]
        e.setdefault("from_patch_id", from_key)
        e.setdefault("to_patch_id", to_key)
        if not e.get("run_id"):
            p = patch_by_key.get(from_key)
            if p and p.get("run_id"):
                e["run_id"] = p["run_id"]
            else:
                e["run_id"] = _infer_run_id_from_patch_from(e.get("_from", ""))

    _write_jsonl(output_dir / "ig_patch_runs.jsonl", runs)
    _write_jsonl(output_dir / "ig_chiral_patches.jsonl", patches)
    _write_jsonl(output_dir / "ig_patch_spectral_signatures.jsonl", spectral)
    _write_jsonl(output_dir / "ig_patch_members.jsonl", members)
    _write_jsonl(output_dir / "ig_patch_edges.jsonl", edges)

    return {
        "ok": True,
        "input_dir": str(input_dir),
        "output_dir": str(output_dir),
        "counts": {
            "ig_patch_runs": len(runs),
            "ig_chiral_patches": len(patches),
            "ig_patch_spectral_signatures": len(spectral),
            "ig_patch_members": len(members),
            "ig_patch_edges": len(edges),
        },
    }
