from __future__ import annotations

import json
from pathlib import Path

from tools.observability.socket_debt_ledger import (
    build_graph,
    classify_socket,
    local_proof_candidates,
    main as socket_ledger_main,
    ranked_ownerless_rows,
    socket_rows,
    write_json,
    write_markdown,
)


def write_lean(path: Path, text: str) -> None:
    path.parent.mkdir(parents=True, exist_ok=True)
    path.write_text(text, encoding="utf-8")


def test_socket_ledger_classifies_ownerless_and_bridge_backed(tmp_path: Path) -> None:
    root = tmp_path / "lean" / "InfoGeometry"
    ownerless_file = root / "Arithmetic" / "Ownerless.lean"
    bridge_file = root / "Canonical" / "BridgeBacked.lean"

    write_lean(
        ownerless_file,
        """import InfoGeometry.Meta.SocketTarget

namespace InfoGeometry.Arithmetic.Ownerless

@[socket_debt_tag]
structure AlphaSocket where
  witness : Nat

end InfoGeometry.Arithmetic.Ownerless
""",
    )
    write_lean(
        bridge_file,
        """import InfoGeometry.Meta.OwnerTarget
import InfoGeometry.Meta.SocketTarget

namespace InfoGeometry.Canonical.BridgeBacked

@[owner_target_tag]
def BridgeBackedOwnerTarget : Prop :=
  True

@[bridge_target_tag]
theorem bridge_backed_transport :
    True := by
  trivial

@[socket_debt_tag]
structure BetaSocket where
  witness : Nat

end InfoGeometry.Canonical.BridgeBacked
""",
    )

    graph = build_graph(root, wl_rounds=1)
    rows = socket_rows(graph)

    by_name = {row["fqname"]: row for row in rows}
    assert set(by_name) == {
        "InfoGeometry.Arithmetic.Ownerless.AlphaSocket",
        "InfoGeometry.Canonical.BridgeBacked.BetaSocket",
    }
    assert by_name["InfoGeometry.Arithmetic.Ownerless.AlphaSocket"]["status"] == "ownerless_socket"
    assert by_name["InfoGeometry.Canonical.BridgeBacked.BetaSocket"]["status"] == "bridge_backed_socket"
    assert classify_socket(rows[0], {rows[0]["file"]: {"owner": 0, "bridge": 0, "socket": 1}}) == "ownerless_socket"
    assert classify_socket(rows[1], {rows[1]["file"]: {"owner": 1, "bridge": 1, "socket": 1}}) == "bridge_backed_socket"


def test_socket_ledger_writes_json_and_markdown(tmp_path: Path) -> None:
    root = tmp_path / "lean" / "InfoGeometry"
    write_lean(
        root / "Arithmetic" / "Ownerless.lean",
        """import InfoGeometry.Meta.SocketTarget

namespace InfoGeometry.Arithmetic.Ownerless

@[socket_debt_tag]
structure AlphaSocket where
  witness : Nat

end InfoGeometry.Arithmetic.Ownerless
""",
    )
    write_lean(
        root / "Canonical" / "BridgeBacked.lean",
        """import InfoGeometry.Meta.OwnerTarget
import InfoGeometry.Meta.SocketTarget

namespace InfoGeometry.Canonical.BridgeBacked

@[owner_target_tag]
def BridgeBackedOwnerTarget : Prop :=
  True

@[bridge_target_tag]
theorem bridge_backed_transport :
    True := by
  trivial

@[socket_debt_tag]
structure BetaSocket where
  witness : Nat

end InfoGeometry.Canonical.BridgeBacked
""",
    )

    graph = build_graph(root, wl_rounds=1)
    rows = socket_rows(graph)

    out_dir = tmp_path / "out"
    out_dir.mkdir()
    json_path = out_dir / "socket_debt_ledger.json"
    md_path = out_dir / "socket_debt_ledger.md"
    write_json(graph, rows, json_path)
    write_markdown(graph, rows, md_path)

    payload = json.loads(json_path.read_text(encoding="utf-8"))
    markdown = md_path.read_text(encoding="utf-8")

    assert payload["socket_count"] == 2
    assert payload["ownerless_socket_count"] == 1
    assert payload["bridge_backed_socket_count"] == 1
    assert {row["status"] for row in payload["sockets"]} == {
        "ownerless_socket",
        "bridge_backed_socket",
    }
    assert "Socket Debt Ledger" in markdown
    assert "Ownerless sockets" in markdown
    assert "Bridge-backed sockets" in markdown


def test_socket_ledger_ranks_root_first_and_finds_candidates(tmp_path: Path) -> None:
    root_rows = [
        {
            "status": "ownerless_socket",
            "fqname": "InfoGeometry.Arithmetic.Root.RootSocket",
            "file": "Arithmetic/Root.lean",
            "name": "RootSocket",
            "direct_dependencies": [],
            "reverse_dependencies": ["u1", "u2", "u3"],
            "file_owner_count": 0,
            "file_bridge_count": 0,
            "file_socket_count": 2,
        },
        {
            "status": "ownerless_socket",
            "fqname": "InfoGeometry.Arithmetic.Root.CrownSocket",
            "file": "Arithmetic/Root.lean",
            "name": "CrownSocket",
            "direct_dependencies": ["d1", "d2", "d3"],
            "reverse_dependencies": ["u1"],
            "file_owner_count": 0,
            "file_bridge_count": 0,
            "file_socket_count": 2,
        },
    ]
    assert ranked_ownerless_rows(root_rows)[0]["fqname"] == "InfoGeometry.Arithmetic.Root.RootSocket"

    root = tmp_path / "lean" / "InfoGeometry"
    write_lean(
        root / "Arithmetic" / "HighImpact.lean",
        """import InfoGeometry.Meta.SocketTarget

namespace InfoGeometry.Arithmetic.HighImpact

@[socket_debt_tag]
structure WittenSocket where
  witness : Nat

@[socket_debt_tag]
structure GammaSocket where
  witness : Nat

theorem WittenBridge :
    True := by
  trivial

theorem GammaBridge :
    True := by
  trivial

end InfoGeometry.Arithmetic.HighImpact
""",
    )
    write_lean(
        root / "Canonical" / "BridgeBacked.lean",
        """import InfoGeometry.Meta.OwnerTarget
import InfoGeometry.Meta.SocketTarget

namespace InfoGeometry.Canonical.BridgeBacked

@[owner_target_tag]
def BridgeBackedOwnerTarget : Prop :=
  True

@[bridge_target_tag]
theorem WittenBridgeWitness :
    True := by
  trivial

@[bridge_target_tag]
theorem GammaBridgeWitness :
    True := by
  trivial

@[socket_debt_tag]
structure DeltaSocket where
  witness : Nat

end InfoGeometry.Canonical.BridgeBacked
""",
    )

    graph = build_graph(root, wl_rounds=1)
    rows = socket_rows(graph)
    ranked = ranked_ownerless_rows(rows)
    candidates = local_proof_candidates(graph, rows)

    assert {row["fqname"] for row in ranked[:2]} == {
        "InfoGeometry.Arithmetic.HighImpact.WittenSocket",
        "InfoGeometry.Arithmetic.HighImpact.GammaSocket",
    }
    assert "InfoGeometry.Arithmetic.HighImpact.WittenSocket" in candidates
    assert candidates["InfoGeometry.Arithmetic.HighImpact.WittenSocket"][0]["is_owner"] is True
    assert any(cand["is_bridge"] for cand in candidates["InfoGeometry.Arithmetic.HighImpact.WittenSocket"])


def test_socket_ledger_main_runs_on_repo_tree(tmp_path: Path) -> None:
    out_dir = tmp_path / "ledger"
    rc = socket_ledger_main(
        [
            "lean/InfoGeometry",
            "--out-dir",
            str(out_dir),
            "--wl-rounds",
            "1",
        ]
    )
    assert rc == 0
    assert (out_dir / "socket_debt_ledger.json").exists()
    assert (out_dir / "socket_debt_ledger.md").exists()
