"""Compatibility wrapper for shared Arango environment loading.

The canonical implementation lives in ``igf.config``. This module remains so
legacy tools can keep importing ``tools.infra.arango_env`` while the ownership
surface moves into the package.
"""

from __future__ import annotations

import os
import sys
from pathlib import Path


_REPO_ROOT = Path(__file__).resolve().parents[2]
_SRC = _REPO_ROOT / "src"
if str(_SRC) not in sys.path:
    sys.path.insert(0, str(_SRC))

from igf.config import (  # noqa: E402
    DEFAULT_ARANGO_DATABASE,
    DEFAULT_ARANGO_ENDPOINT,
    DEFAULT_ARANGO_ENV,
    DEFAULT_ALEXANDRIA_ARANGO_ENDPOINT,
    DEFAULT_HIVE_ARANGO_ENDPOINT,
    arango_database,
    arango_endpoint,
    arango_password,
    arango_username,
    alexandria_arango_database,
    alexandria_arango_endpoint,
    alexandria_arango_password,
    alexandria_arango_username,
    hive_arango_database,
    hive_arango_endpoint,
    hive_arango_password,
    hive_arango_username,
    load_repo_arango_env,
    repo_root_from,
)

__all__ = [
    "DEFAULT_ARANGO_DATABASE",
    "DEFAULT_ARANGO_ENDPOINT",
    "DEFAULT_ARANGO_ENV",
    "DEFAULT_ALEXANDRIA_ARANGO_ENDPOINT",
    "DEFAULT_HIVE_ARANGO_ENDPOINT",
    "arango_database",
    "arango_endpoint",
    "arango_password",
    "arango_username",
    "alexandria_arango_database",
    "alexandria_arango_endpoint",
    "alexandria_arango_password",
    "alexandria_arango_username",
    "hive_arango_database",
    "hive_arango_endpoint",
    "hive_arango_password",
    "hive_arango_username",
    "load_repo_arango_env",
    "os",
    "repo_root_from",
]
