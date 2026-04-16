#!/usr/bin/env python3
"""Shared utilities for deep research controller."""

from __future__ import annotations

import json
import re
from datetime import datetime, timezone
from pathlib import Path
from typing import Any


JSON_BLOCK_RE = re.compile(r"```json\s*(\{.*?\}|\[.*?\])\s*```", re.DOTALL)


def utc_now() -> str:
    return datetime.now(timezone.utc).isoformat()


def to_dict(obj: Any) -> dict[str, Any]:
    if isinstance(obj, dict):
        return obj
    if hasattr(obj, "model_dump"):
        return obj.model_dump()  # type: ignore[no-any-return]
    if hasattr(obj, "to_dict"):
        return obj.to_dict()  # type: ignore[no-any-return]
    return {"repr": repr(obj)}


def output_text(resp: Any) -> str:
    text = getattr(resp, "output_text", None)
    if isinstance(text, str) and text.strip():
        return text
    payload = to_dict(resp)
    text2 = payload.get("output_text")
    if isinstance(text2, str):
        return text2
    return ""


def parse_json_text(text: str) -> Any:
    text = text.strip()
    if not text:
        raise ValueError("empty JSON text")
    try:
        return json.loads(text)
    except json.JSONDecodeError:
        m = JSON_BLOCK_RE.search(text)
        if m:
            return json.loads(m.group(1))
        raise


def load_json(path: Path) -> Any:
    return json.loads(path.read_text(encoding="utf-8"))


def write_json(path: Path, payload: Any) -> None:
    path.parent.mkdir(parents=True, exist_ok=True)
    tmp = path.with_suffix(path.suffix + ".tmp")
    tmp.write_text(json.dumps(payload, indent=2, ensure_ascii=True) + "\n", encoding="utf-8")
    tmp.replace(path)

