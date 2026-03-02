#!/usr/bin/env python3
from __future__ import annotations

import json
import re
from pathlib import Path
from typing import Any


def load_json(path: Path) -> Any:
    return json.loads(path.read_text(encoding="utf-8"))


def dump_json(path: Path, obj: Any) -> None:
    path.parent.mkdir(parents=True, exist_ok=True)
    path.write_text(json.dumps(obj, indent=2, ensure_ascii=False), encoding="utf-8")


def prefix_match(value: str, prefix: str) -> bool:
    return value == prefix or value.startswith(prefix + ".")


def sanitize_label_suffix(name: str) -> str:
    s = name.replace(".", "-").replace("'", "prime")
    s = re.sub(r"[^A-Za-z0-9:_-]+", "-", s)
    s = re.sub(r"-{2,}", "-", s).strip("-")
    return s


def matches_prefix(s: str, prefixes: list[str]) -> bool:
    return any(prefix_match(s, p) for p in prefixes)
