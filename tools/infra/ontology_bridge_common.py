"""Shared helpers for the ArangoDB -> Auto-Ontology projection bridges.

Provides lazy (non-crashing) environment resolution so that ``--help`` and
offline ``--dry-run`` work without requiring Arango or PostgreSQL credentials
to be present in the environment.  Credentials are resolved only when an
actual connection is attempted.
"""

from __future__ import annotations

import os
import sys
from datetime import datetime, timezone
from pathlib import Path
from typing import Any, MutableMapping

_REPO_ROOT = Path(__file__).resolve().parents[2]
_SRC = _REPO_ROOT / "src"
if str(_SRC) not in sys.path:
    sys.path.insert(0, str(_SRC))

from igf.config.env_aliases import (  # noqa: E402
    load_repo_arango_env,
    normalized_arango_env,
)
from igf.config.model import ArangoConfig  # noqa: E402


def resolve_arango_env(database_override: str | None = None) -> tuple[str, str, str, str]:
    """Resolve the legacy bridge tuple without requiring credentials.

    The historical bridge CLIs allow ``--help`` and offline validation to run
    without credentials. Preserve their connection defaults here; actual
    connection callers that require credentials should use
    :func:`get_arango_config`.
    """
    load_repo_arango_env(_REPO_ROOT)
    raw = normalized_arango_env()
    return (
        os.environ.get("ARANGO_ENDPOINT") or raw["endpoint"],
        database_override or os.environ.get("ARANGO_DATABASE") or raw["database"],
        raw["user"] or "root",
        raw["password"],
    )


def get_arango_config() -> ArangoConfig:
    """Resolve validated Arango credentials lazily.

    Loads repo-local env (``configs/local/hive_arango.env`` if present) without
    overriding explicitly set variables, then normalizes aliases. Raises
    :class:`ValueError` if user/password are missing.
    """
    endpoint, database, user, password = resolve_arango_env()
    if not os.environ.get("ARANGO_USER") and not os.environ.get("ARANGO_USERNAME"):
        user = ""
    if not user:
        raise ValueError(
            "ARANGO_USER / ARANGO_USERNAME not set (and no repo-local "
            "hive_arango.env found supplying them)"
        )
    if not password:
        raise ValueError(
            "ARANGO_PASS / ARANGO_PASSWORD not set (and no repo-local "
            "hive_arango.env found supplying them)"
        )
    return ArangoConfig(endpoint=endpoint, database=database, user=user, password=password)


def refresh_legacy_pg_connect(target: MutableMapping[str, Any]) -> MutableMapping[str, Any]:
    """Refresh the legacy CLI's permissive PostgreSQL keyword arguments.

    Unlike :func:`get_pg_connect`, this preserves the old behavior of returning
    empty credentials so import/help and dry-run paths remain usable offline.
    """
    target.update({
        "user": os.environ.get("POSTGRES_USER", ""),
        "password": os.environ.get("POSTGRES_PASSWORD", ""),
        "host": os.environ.get("POSTGRES_HOST", "localhost"),
        "port": os.environ.get("POSTGRES_PORT", "5433"),
        "dbname": os.environ.get("POSTGRES_DATABASE", "auto_ontology"),
    })
    return target


def get_pg_connect() -> dict[str, Any]:
    """Resolve PostgreSQL connection params lazily.

    Reads POSTGRES_* variables from the environment at call time (not import
    time) so that ``--help`` and offline ``--dry-run`` do not crash on missing
    credentials.  Missing required fields raise :class:`ValueError`.
    """
    user = os.environ.get("POSTGRES_USER")
    password = os.environ.get("POSTGRES_PASSWORD")
    if not user:
        raise ValueError("POSTGRES_USER not set")
    if not password:
        raise ValueError("POSTGRES_PASSWORD not set")
    return {
        "user": user,
        "password": password,
        "host": os.environ.get("POSTGRES_HOST", "localhost"),
        "port": os.environ.get("POSTGRES_PORT", "5433"),
        "dbname": os.environ.get("POSTGRES_DATABASE", "auto_ontology"),
        "connect_timeout": int(os.environ.get("POSTGRES_CONNECT_TIMEOUT", "3")),
        "options": "-c search_path=public",
    }


def now_iso() -> str:
    return datetime.now(timezone.utc).isoformat()
