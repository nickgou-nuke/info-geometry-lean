# Frontier Tools

This directory contains the maintained semantic-block and frontier-discovery
tooling.

Canonical entrypoints:
- [semantic_block_export.py](/home/goutev/LEAN4/info-geometry-lean/tools/frontier/semantic_block_export.py)
- [skynet_v2.py](/home/goutev/LEAN4/info-geometry-lean/tools/frontier/skynet_v2.py)
- [extract_module_patch.py](/home/goutev/LEAN4/info-geometry-lean/tools/frontier/extract_module_patch.py)

Use this layer for:
- trusted heavy-module semantic block export
- local and reverse frontier analysis over semantic block JSON
- bridge discovery around large theorem surfaces
- seed-centered module-patch extraction for prompt-ready local LLM context

Outputs from this layer land under `reports/dag/`.

Top-level `tools/semantic_block_export.py` and `tools/skynet_v2.py` remain as
compatibility wrappers, but this directory is the canonical maintained surface.
