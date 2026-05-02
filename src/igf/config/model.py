from __future__ import annotations

from dataclasses import dataclass


@dataclass(frozen=True)
class ArangoConfig:
    endpoint: str
    database: str
    user: str
    password: str
