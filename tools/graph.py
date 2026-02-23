"""Helper routines for working with exported environment graphs."""
from __future__ import annotations

import json
from pathlib import Path
from typing import Any, Iterable, Tuple


def load_graph(path: Path) -> dict[str, Any]:
    """Load a graph JSON produced by ``ExportGraph.lean`` or ``make_graph.py``."""
    data = json.loads(path.read_text(encoding="utf-8"))
    # expect keys 'nodes' and 'edges'
    if not isinstance(data, dict) or 'nodes' not in data or 'edges' not in data:
        raise ValueError(f"unrecognized graph JSON: {path}")
    return data


def edges_as_tuples(data: dict[str, Any]) -> Iterable[Tuple[str, str]]:
    """Return edges list as iterator of (from, to) pairs."""
    for e in data.get('edges', []):
        if isinstance(e, list) or isinstance(e, tuple):
            if len(e) >= 2:
                yield (e[0], e[1])
        elif isinstance(e, dict) and '0' in e and '1' in e:
            yield (e['0'], e['1'])
        else:
            continue


def nodes(data: dict[str, Any]) -> Iterable[str]:
    return list(data.get('nodes', []))
