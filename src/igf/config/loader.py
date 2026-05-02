from __future__ import annotations

from pathlib import Path

from igf.config.env_aliases import load_repo_arango_env, normalized_arango_env
from igf.config.model import ArangoConfig


def load_arango_config(repo_root: Path | None = None) -> ArangoConfig:
    load_repo_arango_env(repo_root)
    raw = normalized_arango_env()
    return ArangoConfig(
        endpoint=raw["endpoint"],
        database=raw["database"],
        user=raw["user"],
        password=raw["password"],
    )
