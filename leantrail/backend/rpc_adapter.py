from __future__ import annotations

from pathlib import Path
from typing import Any


class LeanRPCAdapter:
    """Stub Lean RPC adapter.

    This keeps the endpoint contract in place while the repo decides whether to
    bind to infoview JSON-RPC, an elan-managed server process, or a custom
    declaration/proof-state bridge.
    """

    def __init__(self, repo_root: Path) -> None:
        self.repo_root = repo_root

    def proof_state(self, file: str, line: int, col: int) -> dict[str, Any]:
        return {
            "status": "unavailable",
            "file": file,
            "line": line,
            "col": col,
            "reason": "Lean RPC bridge not yet wired. Endpoint kept for contract compatibility.",
        }
