"""Consumers reconstruct exact dominator ancestry from compact parent links."""

import json

from tools.infra.check_bipartite_bleed import shared_strict_dominator_ids
from tools.infra.generate_source_sink_compression import (
    build_native_lookup,
    strict_dominator_ancestry,
)
from tools.infra.materialize_lossless_infotree import load_lean_structural_topology


def _components():
    return {
        "root": {"componentId": "root", "immediateDominatorComponentId": None},
        "middle": {"componentId": "middle", "immediateDominatorComponentId": "root"},
        "left": {"componentId": "left", "immediateDominatorComponentId": "middle"},
        "right": {"componentId": "right", "immediateDominatorComponentId": "middle"},
    }


def test_parent_chain_expands_exact_strict_ancestors_nearest_first():
    components = _components()
    assert strict_dominator_ancestry("left", components) == ["middle", "root"]
    assert strict_dominator_ancestry("root", components) == []


def test_shared_dominator_intersection_uses_parent_chains():
    components = _components()
    assert shared_strict_dominator_ids({"left", "right"}, components) == ["middle", "root"]


def test_native_lookup_expands_parent_chain_for_selected_declarations():
    payload = {
        "schemaVersion": 2,
        "components": list(_components().values()),
        "membership": [{"declName": "Fixture.left", "componentId": "left"}],
    }
    lookup = build_native_lookup(payload)
    row = lookup["decl_to_component"]["Fixture.left"]
    assert row["strict_dominator_component_ids"] == ["middle", "root"]


def test_arango_topology_loader_preserves_sparse_dominator_parent(tmp_path):
    source = tmp_path / "structural-topology.json"
    source.write_text(json.dumps({
        "schemaVersion": 2,
        "components": [{
            "componentIndex": 0,
            "componentId": "component:child",
            "immediateDominatorComponentId": "component:parent",
            "strictDominatorCount": 1,
        }],
        "membership": [{"declName": "Fixture.child", "componentIndex": 0,
                        "componentId": "component:child"}],
    }), encoding="utf-8")
    _, _, _, metadata, _ = load_lean_structural_topology(
        source, ["Fixture.child"], {"Fixture.child": "raw-child"}
    )
    assert metadata[0]["immediateDominatorComponentId"] == "component:parent"
