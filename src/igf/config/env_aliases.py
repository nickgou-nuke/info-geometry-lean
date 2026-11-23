from __future__ import annotations

import os
import re
from pathlib import Path
from typing import Optional
from urllib.parse import urlsplit


DEFAULT_ARANGO_ENDPOINT = "http://127.0.0.1:8530"
DEFAULT_ALEXANDRIA_ARANGO_ENDPOINT = "http://127.0.0.1:8532"
DEFAULT_ALEXANDRIA_ARANGO_DATABASE = "alexandria"
DEFAULT_HIVE_ARANGO_ENDPOINT = "http://127.0.0.1:8540"
DEFAULT_ARANGO_DATABASE = "infogeometry"
DEFAULT_DARWIN_ARANGO_DATABASE = "darwin_commits"
DEFAULT_HIVE_ARANGO_DATABASE = "hive_live"
DEFAULT_ARANGO_ENV = Path("configs/local/hive_arango.env")
DEFAULT_ALEXANDRIA_ENV = Path("configs/alexandria/.env")
FORBIDDEN_ALEXANDRIA_PORTS = frozenset({8530, 8540})
FORBIDDEN_ALEXANDRIA_DATABASES = frozenset(
    {"infogeometry", "darwin_commits", "hive_live", "aiclaw_auto_rag"}
)

ALIASES = {
    "ARANGO_USER": ("ARANGO_USER", "ARANGO_USERNAME"),
    "ARANGO_PASS": ("ARANGO_PASS", "ARANGO_PASSWORD"),
    "ARANGO_ENDPOINT": ("ARANGO_ENDPOINT",),
    "ARANGO_DATABASE": ("ARANGO_DATABASE",),
}

ALEXANDRIA_ALIASES = {
    "ARANGO_USER": ("ALEXANDRIA_ARANGO_USERNAME", "ALEXANDRIA_ARANGO_USER"),
    "ARANGO_PASS": ("ALEXANDRIA_ARANGO_PASSWORD", "ALEXANDRIA_ARANGO_PASS"),
    "ARANGO_ENDPOINT": ("ALEXANDRIA_ARANGO_ENDPOINT",),
    "ARANGO_DATABASE": ("ALEXANDRIA_ARANGO_DB", "ALEXANDRIA_ARANGO_DATABASE"),
}

HIVE_ALIASES = {
    "ARANGO_USER": ("HIVE_ARANGO_USER", "HIVE_ARANGO_USERNAME", "ARANGO_USER", "ARANGO_USERNAME"),
    "ARANGO_PASS": ("HIVE_ARANGO_PASS", "HIVE_ARANGO_PASSWORD", "ARANGO_PASS", "ARANGO_PASSWORD"),
    # Endpoint selection is lane-specific: generic ARANGO_* belongs to the
    # AST/AQL DAG and must not silently redirect Hive workers.
    "ARANGO_ENDPOINT": ("HIVE_ARANGO_ENDPOINT", "HIVE_ENDPOINT"),
    "ARANGO_DATABASE": ("HIVE_ARANGO_DATABASE", "HIVE_DATABASE"),
}


def repo_root_from(path: Path) -> Path:
    cur = path.resolve()
    for parent in (cur, *cur.parents):
        if (parent / "lakefile.lean").exists() or (parent / "lakefile.toml").exists():
            return parent
    return cur


def _strip_env_value(value: str) -> str:
    value = value.strip()
    if len(value) >= 2 and value[0] == value[-1] and value[0] in {"'", '"'}:
        return value[1:-1]
    return value


def load_repo_arango_env(repo_root: Path | None = None) -> Path | None:
    """Load repo-local Arango credentials without overriding explicit env vars."""
    root = repo_root or repo_root_from(Path.cwd())
    configured = os.environ.get("HIVE_ARANGO_ENV_FILE")
    env_path = Path(configured) if configured else root / DEFAULT_ARANGO_ENV
    if not env_path.exists():
        return None

    for raw_line in env_path.read_text(encoding="utf-8").splitlines():
        line = raw_line.strip()
        if not line or line.startswith("#") or "=" not in line:
            continue
        key, value = line.split("=", 1)
        key = key.strip()
        if not key or not re.fullmatch(r"[A-Za-z_][A-Za-z0-9_]*", key):
            continue
        os.environ.setdefault(key, _strip_env_value(value))

    os.environ.setdefault(
        "ARANGO_ENDPOINT",
        os.environ.get("ARANGO_ENDPOINT", DEFAULT_ARANGO_ENDPOINT),
    )
    os.environ.setdefault(
        "ARANGO_DATABASE",
        os.environ.get("ARANGO_DATABASE", DEFAULT_ARANGO_DATABASE),
    )
    user = os.environ.get("ARANGO_USER") or os.environ.get("ARANGO_USERNAME")
    password = os.environ.get("ARANGO_PASS") or os.environ.get("ARANGO_PASSWORD")
    if user is not None:
        os.environ.setdefault("ARANGO_USER", user)
        os.environ.setdefault("ARANGO_USERNAME", user)
        os.environ.setdefault("HIVE_ARANGO_USER", os.environ.get("HIVE_ARANGO_USER", user))
        os.environ.setdefault("HIVE_ARANGO_USERNAME", os.environ.get("HIVE_ARANGO_USERNAME", user))
    if password is not None:
        os.environ.setdefault("ARANGO_PASS", password)
        os.environ.setdefault("ARANGO_PASSWORD", password)
        os.environ.setdefault("HIVE_ARANGO_PASS", os.environ.get("HIVE_ARANGO_PASS", password))
        os.environ.setdefault("HIVE_ARANGO_PASSWORD", os.environ.get("HIVE_ARANGO_PASSWORD", password))
    os.environ.setdefault(
        "HIVE_ARANGO_ENDPOINT",
        os.environ.get("HIVE_ARANGO_ENDPOINT", DEFAULT_HIVE_ARANGO_ENDPOINT),
    )
    os.environ.setdefault("HIVE_ENDPOINT", os.environ.get("HIVE_ENDPOINT", os.environ["HIVE_ARANGO_ENDPOINT"]))
    os.environ.setdefault(
        "HIVE_ARANGO_DATABASE",
        os.environ.get("HIVE_ARANGO_DATABASE") or os.environ.get("HIVE_DATABASE") or DEFAULT_HIVE_ARANGO_DATABASE,
    )
    os.environ.setdefault("HIVE_DATABASE", os.environ["HIVE_ARANGO_DATABASE"])
    return env_path


def load_alexandria_arango_env(repo_root: Path | None = None) -> Path | None:
    """Load Alexandria-lane Arango settings without touching ARANGO_* or HIVE_*."""
    root = repo_root or repo_root_from(Path.cwd())
    configured = os.environ.get("ALEXANDRIA_ARANGO_ENV_FILE")
    env_path = Path(configured) if configured else root / DEFAULT_ALEXANDRIA_ENV

    had_db = bool(get_env_alias(*ALEXANDRIA_ALIASES["ARANGO_DATABASE"]))
    had_user = bool(get_env_alias(*ALEXANDRIA_ALIASES["ARANGO_USER"]))
    had_pass = bool(get_env_alias(*ALEXANDRIA_ALIASES["ARANGO_PASS"]))
    had_ep = bool(
        get_env_alias(*ALEXANDRIA_ALIASES["ARANGO_ENDPOINT"])
        or os.environ.get("ALEXANDRIA_ARANGO_PORT", "").strip()
    )

    if not env_path.exists():
        if not get_env_alias(*ALEXANDRIA_ALIASES["ARANGO_ENDPOINT"]):
            port = os.environ.get("ALEXANDRIA_ARANGO_PORT", "").strip()
            if port:
                os.environ["ALEXANDRIA_ARANGO_ENDPOINT"] = f"http://127.0.0.1:{port}"
        return None

    root_password = ""
    for raw_line in env_path.read_text(encoding="utf-8").splitlines():
        line = raw_line.strip()
        if not line or line.startswith("#") or "=" not in line:
            continue
        key, value = line.split("=", 1)
        key = key.strip()
        if not key or not re.fullmatch(r"[A-Za-z_][A-Za-z0-9_]*", key):
            continue
        cleaned = _strip_env_value(value)
        if key == "ARANGO_ROOT_PASSWORD":
            if not root_password:
                root_password = cleaned
            continue
        if key.startswith("ALEXANDRIA_"):
            if key in ALEXANDRIA_ALIASES["ARANGO_DATABASE"] and had_db:
                continue
            if key in ALEXANDRIA_ALIASES["ARANGO_USER"] and had_user:
                continue
            if key in ALEXANDRIA_ALIASES["ARANGO_PASS"] and had_pass:
                continue
            if key in ("ALEXANDRIA_ARANGO_ENDPOINT", "ALEXANDRIA_ARANGO_PORT") and had_ep:
                continue
            os.environ.setdefault(key, cleaned)

    if root_password and not get_env_alias(*ALEXANDRIA_ALIASES["ARANGO_PASS"]):
        os.environ["ALEXANDRIA_ARANGO_PASSWORD"] = root_password

    if not get_env_alias(*ALEXANDRIA_ALIASES["ARANGO_ENDPOINT"]):
        port = os.environ.get("ALEXANDRIA_ARANGO_PORT", "").strip()
        default_endpoint = f"http://127.0.0.1:{port}" if port else DEFAULT_ALEXANDRIA_ARANGO_ENDPOINT
        os.environ["ALEXANDRIA_ARANGO_ENDPOINT"] = default_endpoint

    if not get_env_alias(*ALEXANDRIA_ALIASES["ARANGO_DATABASE"]):
        os.environ["ALEXANDRIA_ARANGO_DB"] = DEFAULT_ALEXANDRIA_ARANGO_DATABASE

    if not get_env_alias(*ALEXANDRIA_ALIASES["ARANGO_USER"]):
        os.environ["ALEXANDRIA_ARANGO_USERNAME"] = "root"

    return env_path


def guard_alexandria_target(endpoint: str, database: str) -> None:
    """Reject non-Alexandria ports (:8530, :8540) and non-Alexandria databases."""
    ep_clean = str(endpoint or "").strip()
    db_clean = str(database or "").strip()
    if not ep_clean:
        raise ValueError("Alexandria Arango endpoint must be non-empty.")
    if not db_clean:
        raise ValueError("Alexandria Arango database must be non-empty.")
    if db_clean.lower() in FORBIDDEN_ALEXANDRIA_DATABASES:
        raise ValueError(
            f"Refusing Alexandria target database {db_clean!r}: belongs to a non-Alexandria lane "
            f"(forbidden: {sorted(FORBIDDEN_ALEXANDRIA_DATABASES)})."
        )

    candidate = ep_clean if "://" in ep_clean else f"http://{ep_clean}"
    parsed = urlsplit(candidate)
    if not parsed.hostname:
        raise ValueError(f"Invalid Alexandria endpoint (missing hostname): {endpoint!r}")
    port = parsed.port
    if port in FORBIDDEN_ALEXANDRIA_PORTS:
        raise ValueError(
            f"Refusing Alexandria endpoint {endpoint!r} on forbidden port {port}: "
            "this port belongs to a non-Alexandria lane; use :8532 for Alexandria."
        )


def get_env_alias(*names: str) -> str:
    for name in names:
        value = os.environ.get(name)
        if value:
            return value
    return ""


def normalized_arango_env() -> dict[str, str]:
    endpoint = get_env_alias(*ALIASES["ARANGO_ENDPOINT"]) or DEFAULT_ARANGO_ENDPOINT
    database = get_env_alias(*ALIASES["ARANGO_DATABASE"]) or DEFAULT_ARANGO_DATABASE
    user = get_env_alias(*ALIASES["ARANGO_USER"])
    password = get_env_alias(*ALIASES["ARANGO_PASS"])
    return {
        "endpoint": endpoint.rstrip("/"),
        "database": database,
        "user": user,
        "password": password,
    }


def normalized_hive_arango_env() -> dict[str, str]:
    endpoint = get_env_alias(*HIVE_ALIASES["ARANGO_ENDPOINT"]) or DEFAULT_HIVE_ARANGO_ENDPOINT
    database = get_env_alias(*HIVE_ALIASES["ARANGO_DATABASE"]) or DEFAULT_HIVE_ARANGO_DATABASE
    user = get_env_alias(*HIVE_ALIASES["ARANGO_USER"])
    password = get_env_alias(*HIVE_ALIASES["ARANGO_PASS"])
    return {
        "endpoint": endpoint.rstrip("/"),
        "database": database,
        "user": user,
        "password": password,
    }


def normalized_darwin_arango_env() -> dict[str, str]:
    """Resolve the Darwin commit/evolution database role consistently.

    Darwin shares the generic Arango endpoint and credentials by default, but
    its database is deliberately separate from the declaration/InfoTree
    database. Dedicated DARWIN_ARANGO_* values take precedence.
    """
    endpoint = get_env_alias("DARWIN_ARANGO_ENDPOINT") or arango_endpoint()
    database = get_env_alias("DARWIN_ARANGO_DATABASE") or DEFAULT_DARWIN_ARANGO_DATABASE
    user = get_env_alias("DARWIN_ARANGO_USER", "DARWIN_ARANGO_USERNAME") or arango_username()
    password = get_env_alias("DARWIN_ARANGO_PASS", "DARWIN_ARANGO_PASSWORD") or arango_password()
    return {
        "endpoint": endpoint.rstrip("/"),
        "database": database,
        "user": user,
        "password": password,
    }


def first_present_name(*names: str) -> Optional[str]:
    for name in names:
        if os.environ.get(name):
            return name
    return None


def arango_endpoint(default: str = DEFAULT_ARANGO_ENDPOINT) -> str:
    return os.environ.get("ARANGO_ENDPOINT", default)


def arango_database(default: str = DEFAULT_ARANGO_DATABASE) -> str:
    return os.environ.get("ARANGO_DATABASE", default)


def arango_username(default: str = "root") -> str:
    return os.environ.get("ARANGO_USER") or os.environ.get("ARANGO_USERNAME") or default


def arango_password(default: str = "") -> str:
    return os.environ.get("ARANGO_PASS") or os.environ.get("ARANGO_PASSWORD") or default


def hive_arango_endpoint(default: str = DEFAULT_HIVE_ARANGO_ENDPOINT) -> str:
    return get_env_alias(*HIVE_ALIASES["ARANGO_ENDPOINT"]) or default


def hive_arango_database(default: str = DEFAULT_HIVE_ARANGO_DATABASE) -> str:
    return get_env_alias(*HIVE_ALIASES["ARANGO_DATABASE"]) or default


def hive_arango_username(default: str = "root") -> str:
    return get_env_alias(*HIVE_ALIASES["ARANGO_USER"]) or default


def hive_arango_password(default: str = "") -> str:
    return get_env_alias(*HIVE_ALIASES["ARANGO_PASS"]) or default


def alexandria_arango_endpoint(default: str = DEFAULT_ALEXANDRIA_ARANGO_ENDPOINT) -> str:
    explicit = get_env_alias(*ALEXANDRIA_ALIASES["ARANGO_ENDPOINT"])
    if explicit:
        return explicit
    port = os.environ.get("ALEXANDRIA_ARANGO_PORT", "").strip()
    if port:
        return f"http://127.0.0.1:{port}"
    return default


def alexandria_arango_database(default: str = DEFAULT_ALEXANDRIA_ARANGO_DATABASE) -> str:
    return get_env_alias(*ALEXANDRIA_ALIASES["ARANGO_DATABASE"]) or default


def alexandria_arango_username(default: str = "root") -> str:
    return get_env_alias(*ALEXANDRIA_ALIASES["ARANGO_USER"]) or default


def alexandria_arango_password(default: str = "") -> str:
    return get_env_alias(*ALEXANDRIA_ALIASES["ARANGO_PASS"]) or default


def normalized_alexandria_arango_env() -> dict[str, str]:
    endpoint = alexandria_arango_endpoint()
    database = alexandria_arango_database()
    user = alexandria_arango_username()
    password = alexandria_arango_password()
    return {
        "endpoint": endpoint.rstrip("/"),
        "database": database,
        "user": user,
        "password": password,
    }
