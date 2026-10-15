"""
Unified JSON and JSONL Streaming and I/O utilities for IGF.
Canonical deduplicated implementation for all tools and framework modules.
"""

from __future__ import annotations

import gzip
import hashlib
import json
from pathlib import Path
from typing import Any, Callable, Dict, Generator, Iterable, Iterator, List, Optional, Union


def read_jsonl(path: Union[str, Path]) -> list[dict[str, Any]]:
    """Reads a JSONL file and returns a list of dictionaries."""
    return list(iter_jsonl(path))


def load_strict_jsonl(path: Union[str, Path], required: tuple[str, ...] = ()) -> tuple[list[dict], dict]:
    """Read complete audit input, rejecting malformed rows and invalid UTF-8.

    Blank and `#` comment lines follow the JSONL convention used by this module;
    their count is recorded. Required inputs must exist. Unlike `iter_jsonl`,
    evidence readers never silently drop malformed records.
    """
    p = Path(path)
    digest = hashlib.sha256()
    with p.open("rb") as handle:
        for chunk in iter(lambda: handle.read(1024 * 1024), b""):
            digest.update(chunk)
    opener = gzip.open if str(p).endswith(".gz") else open
    rows = []
    ignored = 0
    def reject_constant(value: str) -> None:
        raise ValueError(f"{p}: nonfinite JSON number {value}")
    with opener(p, "rt", encoding="utf-8", errors="strict") as handle:
        for line_number, line in enumerate(handle, 1):
            if not line.strip() or line.lstrip().startswith("#"):
                ignored += 1
                continue
            try:
                row = json.loads(line, parse_constant=reject_constant)
            except json.JSONDecodeError as exc:
                raise ValueError(f"{p}:{line_number}: invalid JSON") from exc
            if not isinstance(row, dict) or any(key not in row for key in required):
                raise ValueError(f"{p}:{line_number}: invalid object or missing {required}")
            rows.append(row)
    return rows, {"path": str(p.resolve()), "sha256": digest.hexdigest(),
                  "rows": len(rows), "ignored_blank_or_comment_lines": ignored,
                  "required_fields": list(required),
                  "schema_scope": "structural validation; no kernel verification"}


def iter_jsonl(path: Union[str, Path]) -> Iterator[dict[str, Any]]:
    """Iterates over a JSONL (or JSONL.gz) file lazily yielding dicts."""
    p = Path(path)
    if not p.exists():
        return
    is_gz = str(p).endswith(".gz")
    opener = gzip.open if is_gz else open
    with opener(p, "rt", encoding="utf-8", errors="ignore") as f:
        for line in f:
            line_str = line.strip()
            if not line_str or line_str.startswith("#"):
                continue
            try:
                yield json.loads(line_str)
            except Exception:
                continue


def write_jsonl(
    path: Union[str, Path],
    records: Iterable[dict[str, Any]],
    append: bool = False,
    gzip_output: bool = False,
) -> int:
    """Writes an iterable of records to a JSONL (or JSONL.gz) file."""
    p = Path(path)
    if gzip_output and not str(p).endswith(".gz"):
        p = p.with_name(p.name + ".gz")
    p.parent.mkdir(parents=True, exist_ok=True)
    is_gz = str(p).endswith(".gz") or gzip_output
    mode = "at" if append else "wt"
    opener = gzip.open if is_gz else open
    count = 0
    with opener(p, mode, encoding="utf-8") as f:
        for rec in records:
            f.write(json.dumps(rec, ensure_ascii=False) + "\n")
            count += 1
    return count


def load_json(path: Union[str, Path], default: Any = None) -> Any:
    """Loads a JSON file with optional default on error or missing file."""
    p = Path(path)
    if not p.exists():
        return default
    try:
        with p.open("r", encoding="utf-8", errors="ignore") as f:
            return json.load(f)
    except Exception:
        return default


def load_json_dict(path: Union[str, Path]) -> dict[str, Any]:
    """Loads a JSON file returning a dictionary."""
    res = load_json(path, default={})
    return res if isinstance(res, dict) else {}


def dump_json(path: Union[str, Path], data: Any, indent: int = 2) -> None:
    """Dumps data to a pretty-formatted JSON file atomically."""
    p = Path(path)
    p.parent.mkdir(parents=True, exist_ok=True)
    p.write_text(json.dumps(data, indent=indent, ensure_ascii=False) + "\n", encoding="utf-8")
