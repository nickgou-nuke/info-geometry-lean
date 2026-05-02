from __future__ import annotations

import os
from typing import Optional


ALIASES = {
    "ARANGO_USER": ("ARANGO_USER", "ARANGO_USERNAME"),
    "ARANGO_PASS": ("ARANGO_PASS", "ARANGO_PASSWORD"),
    "ARANGO_ENDPOINT": ("ARANGO_ENDPOINT",),
    "ARANGO_DATABASE": ("ARANGO_DATABASE",),
}


def get_env_alias(*names: str) -> str:
    for name in names:
        value = os.environ.get(name)
        if value:
            return value
    return ""


def normalized_arango_env() -> dict[str, str]:
    endpoint = get_env_alias(*ALIASES["ARANGO_ENDPOINT"]) or "http://127.0.0.1:8530"
    database = get_env_alias(*ALIASES["ARANGO_DATABASE"]) or "infogeometry"
    user = get_env_alias(*ALIASES["ARANGO_USER"])
    password = get_env_alias(*ALIASES["ARANGO_PASS"])
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
