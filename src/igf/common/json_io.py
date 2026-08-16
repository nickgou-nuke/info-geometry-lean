"""
Unified JSON and JSONL Streaming and I/O utilities for IGF.
Canonical deduplicated implementation for all tools and framework modules.
"""

from __future__ import annotations

import gzip
import json
from pathlib import Path
from typing import Any, Callable, Dict, Generator, Iterable, Iterator, List, Optional, Union


def read_jsonl(path: Union[str, Path]) -> list[dict[str, Any]]:
    """Reads a JSONL file and returns a list of dictionaries."""
    return list(iter_jsonl(path))


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
