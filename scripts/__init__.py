"""Top-level Python package for InfoGeometry scripting helpers.

This package consolidates the various utility scripts that formerly lived
as independent executables under ``scripts/``.  Importing ``scripts`` makes
submodules available for direct use; the goal is to provide a unified
command-line interface in ``scripts/cli.py``.
"""

from __future__ import annotations

# expose a few commonly-used helpers at package level
from . import utils  # noqa: F401

__all__ = ["utils"]
