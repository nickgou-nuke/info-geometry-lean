from __future__ import annotations

from pathlib import Path
from typing import Any

from igf.config.loader import load_arango_config
from igf.graph.arango_client import connect_db
from igf.pipeline.build import build_chiral_patches
from igf.pipeline.ingest import ingest_artifacts
from igf.pipeline.validate import validate_artifacts
from igf.pipeline.verify import verify_run


def run_offline_pipeline(
    *,
    nodes: Path,
    edges: Path,
    fingerprints: Path | None,
    output_dir: Path,
    schemas_dir: Path,
    run_id: str | None,
    strict: bool,
    ego_limit: int = 40,
    ego_radius: int = 2,
    min_scc_size: int = 2,
    binder_min_size: int = 3,
    max_patch_nodes: int = 128,
    spectral_k: int = 8,
    do_ingest: bool = False,
    do_verify: bool = False,
    verify_limit: int = 25,
) -> dict[str, Any]:
    build = build_chiral_patches(
        nodes=nodes,
        edges=edges,
        fingerprints=fingerprints,
        output_dir=output_dir,
        run_id=run_id,
        ego_limit=ego_limit,
        ego_radius=ego_radius,
        min_scc_size=min_scc_size,
        binder_min_size=binder_min_size,
        max_patch_nodes=max_patch_nodes,
        spectral_k=spectral_k,
    )
    if not build.get("ok"):
        return {"ok": False, "stage": "build", "exit_code": 1, "build": build}

    validation = validate_artifacts(output_dir, schemas_dir, strict=strict)
    if not validation.get("ok"):
        return {
            "ok": False,
            "stage": "validate",
            "exit_code": 1,
            "build": build,
            "validate": validation,
        }

    result: dict[str, Any] = {
        "ok": True,
        "stage": "complete",
        "exit_code": 0,
        "build": build,
        "validate": validation,
    }

    if not (do_ingest or do_verify):
        return result

    cfg = load_arango_config()
    db = connect_db(cfg)

    ingest = ingest_artifacts(db, output_dir)
    result["ingest"] = ingest
    if not ingest.get("ok"):
        result["ok"] = False
        result["stage"] = "ingest"
        result["exit_code"] = 1
        return result

    if do_verify:
        resolved_run_id = run_id or build.get("run_id")
        verify = verify_run(db, resolved_run_id, limit=verify_limit)
        result["verify"] = verify
        if not verify.get("ok"):
            result["ok"] = False
            result["stage"] = "verify"
            result["exit_code"] = 2
            return result

    return result
