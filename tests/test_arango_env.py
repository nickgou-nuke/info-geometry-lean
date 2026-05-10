"""Tests for tools/infra/arango_env.py — ArangoDB environment config wrapper."""
from __future__ import annotations

import os
from pathlib import Path

import pytest

from tools.infra.arango_env import (
    DEFAULT_ARANGO_DATABASE,
    DEFAULT_ARANGO_ENDPOINT,
    DEFAULT_ARANGO_ENV,
    arango_database,
    arango_endpoint,
    arango_password,
    arango_username,
    load_repo_arango_env,
    repo_root_from,
)

REPO_ROOT = Path(__file__).resolve().parents[1]

# Environment variable names (inferred from igf.config.env_aliases)
_ENDPOINT_VAR = "ARANGO_ENDPOINT"
_DATABASE_VAR = "ARANGO_DATABASE"
_USERNAME_VAR = "ARANGO_USERNAME"
_PASSWORD_VAR = "ARANGO_PASSWORD"


# ---------------------------------------------------------------------------
# Defaults when env vars are not set
# ---------------------------------------------------------------------------

def test_arango_endpoint_default(monkeypatch: pytest.MonkeyPatch) -> None:
    monkeypatch.delenv(_ENDPOINT_VAR, raising=False)
    assert arango_endpoint() == DEFAULT_ARANGO_ENDPOINT
    assert arango_endpoint() == "http://127.0.0.1:8530"


def test_arango_database_default(monkeypatch: pytest.MonkeyPatch) -> None:
    monkeypatch.delenv(_DATABASE_VAR, raising=False)
    assert arango_database() == DEFAULT_ARANGO_DATABASE
    assert arango_database() == "infogeometry"


def test_arango_username_default(monkeypatch: pytest.MonkeyPatch) -> None:
    monkeypatch.delenv(_USERNAME_VAR, raising=False)
    assert arango_username() == "root"


def test_arango_password_default(monkeypatch: pytest.MonkeyPatch) -> None:
    monkeypatch.delenv(_PASSWORD_VAR, raising=False)
    assert arango_password() == ""


# ---------------------------------------------------------------------------
# Env var overrides
# ---------------------------------------------------------------------------

def test_arango_endpoint_env_override(monkeypatch: pytest.MonkeyPatch) -> None:
    monkeypatch.setenv(_ENDPOINT_VAR, "http://10.0.0.1:8530")
    assert arango_endpoint() == "http://10.0.0.1:8530"


def test_arango_database_env_override(monkeypatch: pytest.MonkeyPatch) -> None:
    monkeypatch.setenv(_DATABASE_VAR, "testdb")
    assert arango_database() == "testdb"


def test_arango_username_env_override(monkeypatch: pytest.MonkeyPatch) -> None:
    monkeypatch.setenv(_USERNAME_VAR, "admin")
    assert arango_username() == "admin"


def test_arango_password_env_override(monkeypatch: pytest.MonkeyPatch) -> None:
    monkeypatch.setenv(_PASSWORD_VAR, "secret")
    assert arango_password() == "secret"


# ---------------------------------------------------------------------------
# Custom default arg is returned when env var is not set
# ---------------------------------------------------------------------------

def test_arango_endpoint_custom_default(monkeypatch: pytest.MonkeyPatch) -> None:
    monkeypatch.delenv(_ENDPOINT_VAR, raising=False)
    assert arango_endpoint(default="http://custom:9999") == "http://custom:9999"


def test_arango_database_custom_default(monkeypatch: pytest.MonkeyPatch) -> None:
    monkeypatch.delenv(_DATABASE_VAR, raising=False)
    assert arango_database(default="my_db") == "my_db"


# ---------------------------------------------------------------------------
# DEFAULT_ARANGO_ENV
# ---------------------------------------------------------------------------

def test_default_arango_env_is_relative_path() -> None:
    env_path = Path(DEFAULT_ARANGO_ENV)
    assert not env_path.is_absolute()
    assert env_path.suffix == ".env"


# ---------------------------------------------------------------------------
# load_repo_arango_env — resolves env file path
# ---------------------------------------------------------------------------

def test_load_repo_arango_env_returns_path_or_none() -> None:
    result = load_repo_arango_env(REPO_ROOT)
    # May return None if the file doesn't exist, or a Path if it does
    assert result is None or isinstance(result, Path)


def test_load_repo_arango_env_writes_and_reads(tmp_path: Path) -> None:
    env_file = tmp_path / "configs" / "local" / "hive_arango.env"
    env_file.parent.mkdir(parents=True)
    env_file.write_text("ARANGO_DATABASE=testdb\n", encoding="utf-8")
    result = load_repo_arango_env(tmp_path)
    assert result == env_file


# ---------------------------------------------------------------------------
# repo_root_from — walks up to find lakefile.lean
# ---------------------------------------------------------------------------

def test_repo_root_from_workspace() -> None:
    result = repo_root_from(REPO_ROOT / "tools" / "infra")
    assert result == REPO_ROOT


def test_repo_root_from_nested_dir() -> None:
    result = repo_root_from(REPO_ROOT / "src" / "igf" / "config")
    assert result == REPO_ROOT
