from __future__ import annotations

from igf.config.env_aliases import normalized_arango_env
from igf.config.model import ArangoConfig


def load_arango_config() -> ArangoConfig:
    raw = normalized_arango_env()
    return ArangoConfig(
        endpoint=raw["endpoint"],
        database=raw["database"],
        user=raw["user"],
        password=raw["password"],
    )
