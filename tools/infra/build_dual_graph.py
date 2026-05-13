#!/usr/bin/env python3
"""Compatibility wrapper for the canonical wire/gate topology transform.

The production dual graph schema is owned by
``tools/infra/wire_topology_transform.py``.  This wrapper keeps the older
``build_dual_graph.py`` entrypoint available without creating a second,
incompatible Arango schema.
"""

from __future__ import annotations

import argparse
import json
import sys
from pathlib import Path

if __package__ in (None, ""):
    sys.path.insert(0, str(Path(__file__).resolve().parents[2]))
    from tools.infra.wire_topology_transform import DEFAULT_INPUT_DIR, DEFAULT_OUTPUT_DIR, transform
else:
    from tools.infra.wire_topology_transform import DEFAULT_INPUT_DIR, DEFAULT_OUTPUT_DIR, transform


def run(input_dir: Path, output_dir: Path) -> dict:
    return transform(input_dir, output_dir)


def parse_args() -> argparse.Namespace:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--input-dir", type=Path, default=DEFAULT_INPUT_DIR)
    parser.add_argument("--output-dir", type=Path, default=DEFAULT_OUTPUT_DIR)
    return parser.parse_args()


def main() -> int:
    args = parse_args()
    metadata = run(args.input_dir, args.output_dir)
    print(json.dumps(metadata, indent=2, sort_keys=True))
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
