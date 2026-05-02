"""Configuration utilities for igf."""

from igf.config.env_aliases import (
    DEFAULT_ARANGO_DATABASE,
    DEFAULT_ARANGO_ENDPOINT,
    DEFAULT_ARANGO_ENV,
    arango_database,
    arango_endpoint,
    arango_password,
    arango_username,
    first_present_name,
    load_repo_arango_env,
    normalized_arango_env,
    repo_root_from,
)
from igf.config.loader import load_arango_config
from igf.config.model import ArangoConfig

__all__ = [
    "ArangoConfig",
    "DEFAULT_ARANGO_DATABASE",
    "DEFAULT_ARANGO_ENDPOINT",
    "DEFAULT_ARANGO_ENV",
    "arango_database",
    "arango_endpoint",
    "arango_password",
    "arango_username",
    "first_present_name",
    "load_arango_config",
    "load_repo_arango_env",
    "normalized_arango_env",
    "repo_root_from",
]
