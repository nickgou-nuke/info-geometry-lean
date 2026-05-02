from __future__ import annotations

INDEXES: dict[str, tuple[dict, ...]] = {
    "ig_patch_runs": (
        {"fields": ("run_id",), "unique": True},
        {"fields": ("created_at",), "unique": False},
    ),
    "ig_chiral_patches": (
        {"fields": ("run_id", "patch_id"), "unique": True},
        {"fields": ("run_id",), "unique": False},
        {"fields": ("patch_type",), "unique": False},
        {"fields": ("chiral_bias",), "unique": False},
        {"fields": ("chiral_entropy",), "unique": False},
        {"fields": ("coarse_hash",), "unique": False},
    ),
    "ig_patch_spectral_signatures": (
        {"fields": ("run_id", "patch_id"), "unique": True},
    ),
    "ig_patch_members": (
        {"fields": ("run_id", "patch_id"), "unique": False},
    ),
    "ig_patch_edges": (
        {"fields": ("run_id", "from_patch_id", "to_patch_id"), "unique": False},
    ),
}

