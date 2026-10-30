from __future__ import annotations

from pathlib import Path
from unittest.mock import Mock, patch

from tools.infra import refresh_decl_graph


def test_refresh_runs_complete_transaction_inside_shared_build_lock() -> None:
    state = {"locked": False}

    class Lock:
        def __enter__(self):
            state["locked"] = True
            return self

        def __exit__(self, exc_type, exc, traceback):
            state["locked"] = False

    args = Mock()

    def run(args_arg, root_arg, lock_arg):
        assert state["locked"]
        assert args_arg is args
        assert root_arg == Path("/repo")
        assert isinstance(lock_arg, Lock)
        return 23

    with (
        patch.object(refresh_decl_graph, "parse_args", return_value=args),
        patch.object(refresh_decl_graph, "repo_root", return_value=Path("/repo")),
        patch.object(refresh_decl_graph, "acquire_build_lock", return_value=Lock()) as acquire,
        patch.object(refresh_decl_graph, "_run_refresh", side_effect=run),
    ):
        assert refresh_decl_graph.main() == 23

    acquire.assert_called_once()
    assert not state["locked"]
