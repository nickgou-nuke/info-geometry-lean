from __future__ import annotations

VERTEX_COLLECTIONS = {
    "ig_patch_runs",
    "ig_chiral_patches",
    "ig_patch_spectral_signatures",
}

EDGE_COLLECTIONS = {
    "ig_patch_members",
    "ig_patch_edges",
}

ALL_COLLECTIONS = tuple(sorted(VERTEX_COLLECTIONS | EDGE_COLLECTIONS))

