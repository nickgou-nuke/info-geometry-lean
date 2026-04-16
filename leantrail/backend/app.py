"""Compatibility entrypoint for LeanTrail API.

Prefer `python3 -m leantrail.api.server`.
"""

from __future__ import annotations

from leantrail.api.server import main


if __name__ == "__main__":
    raise SystemExit(main())
