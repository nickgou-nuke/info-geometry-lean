"""Shared Python utilities for InfoGeometry tooling.

This package collects helpers used by the various scripts under ``scripts/``
and ``lean/scripts``.  Moving these modules into a proper package makes it
possible to import them consistently from multiple entry points and allows
future tooling to depend on them via a ``python -m`` invocation or a
packaging setup.
"""

__all__ = ["pathing", "graph"]
