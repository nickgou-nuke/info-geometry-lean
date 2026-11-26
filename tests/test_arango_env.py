"""Tests for tools/infra/arango_env.py — ArangoDB environment config wrapper."""
from __future__ import annotations

import os
from pathlib import Path

import pytest

from tools.infra.arango_env import (
    DEFAULT_ALEXANDRIA_ARANGO_DATABASE,
    DEFAULT_ALEXANDRIA_ARANGO_ENDPOINT,
    DEFAULT_ALEXANDRIA_ENV,
    DEFAULT_ARANGO_DATABASE,
    DEFAULT_ARANGO_ENDPOINT,
    DEFAULT_ARANGO_ENV,
    FORBIDDEN_ALEXANDRIA_DATABASES,
    FORBIDDEN_ALEXANDRIA_PORTS,
    alexandria_arango_database,
    alexandria_arango_endpoint,
    alexandria_arango_password,
    alexandria_arango_username,
    arango_database,
    arango_endpoint,
    arango_password,
    arango_username,
    guard_alexandria_target,
    load_alexandria_arango_env,
    load_repo_arango_env,
    normalized_alexandria_arango_env,
    normalized_darwin_arango_env,
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
    monkeypatch.delenv("ARANGO_PASSWORD", raising=False)
    monkeypatch.delenv("ARANGO_PASS", raising=False)
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
    monkeypatch.delenv("ARANGO_USER", raising=False)
    monkeypatch.delenv("ARANGO_PASS", raising=False)
    monkeypatch.setenv(_USERNAME_VAR, "admin")
    assert arango_username() == "admin"


def test_arango_password_env_override(monkeypatch: pytest.MonkeyPatch) -> None:
    monkeypatch.delenv("ARANGO_USER", raising=False)
    monkeypatch.delenv("ARANGO_PASS", raising=False)
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


def test_darwin_arango_config_keeps_database_role_separate(monkeypatch: pytest.MonkeyPatch) -> None:
    for name in (
        "DARWIN_ARANGO_ENDPOINT", "DARWIN_ARANGO_DATABASE", "DARWIN_ARANGO_USER",
        "DARWIN_ARANGO_USERNAME", "DARWIN_ARANGO_PASS", "DARWIN_ARANGO_PASSWORD",
    ):
        monkeypatch.delenv(name, raising=False)
    monkeypatch.setenv("ARANGO_ENDPOINT", "http://generic:8530/")
    monkeypatch.setenv("ARANGO_DATABASE", "infogeometry")
    monkeypatch.setenv("ARANGO_USERNAME", "shared-user")
    monkeypatch.setenv("ARANGO_PASSWORD", "shared-pass")

    config = normalized_darwin_arango_env()

    assert config == {
        "endpoint": "http://generic:8530",
        "database": "darwin_commits",
        "user": "shared-user",
        "password": "shared-pass",
    }


def test_darwin_arango_config_specific_values_override_generic(monkeypatch: pytest.MonkeyPatch) -> None:
    monkeypatch.setenv("ARANGO_DATABASE", "infogeometry")
    monkeypatch.setenv("DARWIN_ARANGO_DATABASE", "darwin_test")
    monkeypatch.setenv("ARANGO_USER", "generic-user")
    monkeypatch.setenv("DARWIN_ARANGO_USERNAME", "darwin-user")
    monkeypatch.setenv("ARANGO_PASS", "generic-pass")
    monkeypatch.setenv("DARWIN_ARANGO_PASSWORD", "darwin-pass")

    config = normalized_darwin_arango_env()

    assert config["database"] == "darwin_test"
    assert config["user"] == "darwin-user"
    assert config["password"] == "darwin-pass"


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


# ---------------------------------------------------------------------------
# Alexandria PDF lane isolation, env loader, and target guard (F1)
# ---------------------------------------------------------------------------

_ALEXANDRIA_VARS = (
    "ALEXANDRIA_ARANGO_ENV_FILE",
    "ALEXANDRIA_ARANGO_ENDPOINT",
    "ALEXANDRIA_ARANGO_PORT",
    "ALEXANDRIA_ARANGO_DB",
    "ALEXANDRIA_ARANGO_DATABASE",
    "ALEXANDRIA_ARANGO_USERNAME",
    "ALEXANDRIA_ARANGO_USER",
    "ALEXANDRIA_ARANGO_PASSWORD",
    "ALEXANDRIA_ARANGO_PASS",
)


def _clear_alexandria_env(monkeypatch: pytest.MonkeyPatch) -> None:
    for var in _ALEXANDRIA_VARS:
        monkeypatch.delenv(var, raising=False)


def test_alexandria_arango_defaults_and_isolation_from_8530_8540(monkeypatch: pytest.MonkeyPatch) -> None:
    _clear_alexandria_env(monkeypatch)
    monkeypatch.setenv("ARANGO_ENDPOINT", "http://127.0.0.1:8530")
    monkeypatch.setenv("ARANGO_DATABASE", "infogeometry")
    monkeypatch.setenv("ARANGO_USER", "infogeo_user")
    monkeypatch.setenv("ARANGO_USERNAME", "infogeo_user")
    monkeypatch.setenv("ARANGO_PASS", "infogeo_secret")
    monkeypatch.setenv("ARANGO_PASSWORD", "infogeo_secret")
    monkeypatch.setenv("HIVE_ARANGO_ENDPOINT", "http://127.0.0.1:8540")
    monkeypatch.setenv("HIVE_ARANGO_DATABASE", "hive_live")

    assert DEFAULT_ALEXANDRIA_ARANGO_ENDPOINT == "http://127.0.0.1:8532"
    assert DEFAULT_ALEXANDRIA_ARANGO_DATABASE == "alexandria"
    assert DEFAULT_ALEXANDRIA_ENV == Path("configs/alexandria/.env")
    assert FORBIDDEN_ALEXANDRIA_PORTS == frozenset({8530, 8540})
    assert {"infogeometry", "darwin_commits", "hive_live", "aiclaw_auto_rag"} <= FORBIDDEN_ALEXANDRIA_DATABASES

    assert alexandria_arango_endpoint() == "http://127.0.0.1:8532"
    assert alexandria_arango_database() == "alexandria"
    assert alexandria_arango_username() == "root"
    assert alexandria_arango_password() == ""
    assert normalized_alexandria_arango_env() == {
        "endpoint": "http://127.0.0.1:8532",
        "database": "alexandria",
        "user": "root",
        "password": "",
    }


def test_load_alexandria_arango_env_derives_endpoint_and_preserves_non_alexandria_vars(
    tmp_path: Path, monkeypatch: pytest.MonkeyPatch
) -> None:
    _clear_alexandria_env(monkeypatch)
    monkeypatch.setenv("ARANGO_ENDPOINT", "http://127.0.0.1:8530")
    monkeypatch.setenv("ARANGO_DATABASE", "infogeometry")
    monkeypatch.setenv("ARANGO_USER", "infogeo_user")
    monkeypatch.setenv("ARANGO_PASS", "infogeo_pass")

    env_file = tmp_path / "configs" / "alexandria" / ".env"
    env_file.parent.mkdir(parents=True)
    env_file.write_text(
        "\n".join(
            [
                "ARANGO_ROOT_PASSWORD=from_root_pw",
                "ALEXANDRIA_ARANGO_PORT=8532",
                "ALEXANDRIA_ARANGO_DB=alexandria",
                "ALEXANDRIA_ARANGO_USERNAME=alex_user",
            ]
        )
        + "\n",
        encoding="utf-8",
    )

    loaded = load_alexandria_arango_env(tmp_path)
    assert loaded == env_file
    assert alexandria_arango_endpoint() == "http://127.0.0.1:8532"
    assert alexandria_arango_database() == "alexandria"
    assert alexandria_arango_username() == "alex_user"
    assert alexandria_arango_password() == "from_root_pw"
    # Must never overwrite or mutate InfoTree :8530 env vars
    assert os.environ["ARANGO_ENDPOINT"] == "http://127.0.0.1:8530"
    assert os.environ["ARANGO_DATABASE"] == "infogeometry"
    assert os.environ["ARANGO_USER"] == "infogeo_user"
    assert os.environ["ARANGO_PASS"] == "infogeo_pass"


def test_load_alexandria_arango_env_respects_explicit_override_and_missing_file(
    tmp_path: Path, monkeypatch: pytest.MonkeyPatch
) -> None:
    _clear_alexandria_env(monkeypatch)
    assert load_alexandria_arango_env(tmp_path) is None

    custom_env = tmp_path / "custom_alex.env"
    custom_env.write_text(
        "ALEXANDRIA_ARANGO_PORT=8599\nALEXANDRIA_ARANGO_PASSWORD=file_pw\n",
        encoding="utf-8",
    )
    monkeypatch.setenv("ALEXANDRIA_ARANGO_ENV_FILE", str(custom_env))
    monkeypatch.setenv("ALEXANDRIA_ARANGO_PASSWORD", "explicit_pw")
    monkeypatch.setenv("ALEXANDRIA_ARANGO_DATABASE", "custom_alex_db")

    loaded = load_alexandria_arango_env(tmp_path)
    assert loaded == custom_env
    assert alexandria_arango_endpoint() == "http://127.0.0.1:8599"
    assert alexandria_arango_password() == "explicit_pw"
    assert alexandria_arango_database() == "custom_alex_db"


@pytest.mark.parametrize(
    "endpoint,database",
    [
        ("http://127.0.0.1:8530", "alexandria"),
        ("https://127.0.0.1:8530/", "alexandria"),
        ("http://127.0.0.1:8530/some/path", "alexandria"),
        ("127.0.0.1:8530", "alexandria"),
        ("[::1]:8530", "alexandria"),
        ("http://root:pw@127.0.0.1:8530", "alexandria"),
        ("http://127.0.0.1:8540", "alexandria"),
        ("[::1]:8540", "alexandria"),
        ("http://127.0.0.1:8532", "infogeometry"),
        ("http://127.0.0.1:8532", "InfoGeometry"),
        ("http://127.0.0.1:8532", "darwin_commits"),
        ("http://127.0.0.1:8532", "hive_live"),
        ("http://127.0.0.1:8532", "aiclaw_auto_rag"),
        ("", "alexandria"),
        ("http://127.0.0.1:8532", ""),
        ("http:///nohost:8532", "alexandria"),
        ("http://127.0.0.1:99999", "alexandria"),
    ],
)
def test_guard_alexandria_target_rejects_forbidden_targets(endpoint: str, database: str) -> None:
    with pytest.raises(ValueError):
        guard_alexandria_target(endpoint, database)


def test_guard_alexandria_target_accepts_8532_alexandria() -> None:
    guard_alexandria_target("http://127.0.0.1:8532", "alexandria")
    guard_alexandria_target("http://127.0.0.1:8532/", "alexandria_test")


def test_load_alexandria_arango_env_does_not_shadow_explicit_database_or_port(
    tmp_path: Path, monkeypatch: pytest.MonkeyPatch
) -> None:
    _clear_alexandria_env(monkeypatch)
    env_file = tmp_path / "configs" / "alexandria" / ".env"
    env_file.parent.mkdir(parents=True)
    env_file.write_text(
        "\n".join(
            [
                "ARANGO_ROOT_PASSWORD=from_root_pw",
                "ALEXANDRIA_ARANGO_PORT=8532",
                "ALEXANDRIA_ARANGO_DB=alexandria",
                "ALEXANDRIA_ARANGO_USERNAME=file_user",
            ]
        )
        + "\n",
        encoding="utf-8",
    )

    monkeypatch.setenv("ALEXANDRIA_ARANGO_DATABASE", "dedicated_dag_db")
    monkeypatch.setenv("ALEXANDRIA_ARANGO_PORT", "8538")

    loaded = load_alexandria_arango_env(tmp_path)
    assert loaded == env_file
    assert alexandria_arango_database() == "dedicated_dag_db"
    assert alexandria_arango_endpoint() == "http://127.0.0.1:8538"
    assert alexandria_arango_username() == "file_user"
    assert alexandria_arango_password() == "from_root_pw"


def test_alexandria_port_8538_defaults_to_dag_brain_database(
    tmp_path: Path, monkeypatch: pytest.MonkeyPatch
) -> None:
    _clear_alexandria_env(monkeypatch)
    monkeypatch.setenv("ALEXANDRIA_ARANGO_PORT", "8538")
    assert load_alexandria_arango_env(tmp_path) is None
    assert alexandria_arango_endpoint() == "http://127.0.0.1:8538"
    assert alexandria_arango_database() == "alexandria_dag_brain"
    assert normalized_alexandria_arango_env() == {
        "endpoint": "http://127.0.0.1:8538",
        "database": "alexandria_dag_brain",
        "user": "root",
        "password": "",
    }


def test_alexandria_arango_endpoint_derives_from_port_without_env_file(
    tmp_path: Path, monkeypatch: pytest.MonkeyPatch
) -> None:
    _clear_alexandria_env(monkeypatch)
    monkeypatch.setenv("ALEXANDRIA_ARANGO_PORT", "8538")
    assert load_alexandria_arango_env(tmp_path) is None
    assert alexandria_arango_endpoint() == "http://127.0.0.1:8538"
    assert os.environ["ALEXANDRIA_ARANGO_ENDPOINT"] == "http://127.0.0.1:8538"

