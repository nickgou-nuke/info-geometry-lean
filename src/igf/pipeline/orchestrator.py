from __future__ import annotations

from pathlib import Path
from typing import Any

from igf.pipeline.build import build_chiral_patches
from igf.pipeline.validate import validate_artifacts


def run_offline_pipeline(
    *,
    nodes: Path,
    edges: Path,
    fingerprints: Path | None,
    output_dir: Path,
    schemas_dir: Path,
    run_id: str | None,
    strict: bool,
) -> dict[str, Any]:
    build = build_chiral_patches(
        nodes=nodes,
        edges=edges,
        fingerprints=fingerprints,
        output_dir=output_dir,
        run_id=run_id,
    )
    if not build.get("ok"):
        return {"ok": False, "stage": "build", "build": build}

    validation = validate_artifacts(output_dir, schemas_dir, strict=strict)
    return {
        "ok": bool(validation.get("ok")),
        "stage": "complete" if validation.get("ok") else "validate",
        "build": build,
        "validate": validation,
    }
