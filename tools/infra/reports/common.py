from __future__ import annotations

import datetime as dt
import json
import sys
from pathlib import Path
from typing import Any

if __package__ in (None, ""):
    sys.path.insert(0, str(Path(__file__).resolve().parents[3]))
    from tools.pathing import repo_root
else:
    from tools.pathing import repo_root


def normalize_user_path(path: str | None, default: Path) -> Path:
    if not path:
        return default
    candidate = Path(path)
    if candidate.is_absolute():
        return candidate
    return (repo_root() / candidate).resolve()


def load_json(path: Path) -> dict[str, Any]:
    return json.loads(path.read_text(encoding="utf-8"))


def read_text(path: Path) -> str:
    if not path.exists():
        raise SystemExit(f"missing required input: {path}")
    return path.read_text(encoding="utf-8").strip()


def write_text(path: Path, text: str) -> None:
    path.parent.mkdir(parents=True, exist_ok=True)
    path.write_text(text, encoding="utf-8")


def relpath(path: Path, root: Path) -> str:
    return str(path.relative_to(root))


def generated_timestamp() -> str:
    return dt.datetime.now().strftime("%Y-%m-%d %H:%M:%S")
