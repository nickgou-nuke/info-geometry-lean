"""Tests for tools/infra/causal_cone_spectrum.py against a synthetic mock DAG."""
import sys
from pathlib import Path

# ensure tools/ is importable
sys.path.insert(0, str(Path(__file__).resolve().parents[1] / "tools" / "infra"))
sys.path.insert(0, str(Path(__file__).resolve().parents[1] / "tools"))

import pytest

from causal_cone_spectrum import (
    past_cone_bfs,
    forward_cone_bfs,
    shell_decomposition,
    component_signature,
    component_own_parities,
    precompute_signatures,
    precompute_own_parities,
    role_overlay,
    find_binding_witnesses,
    declaration_mass,
    binding_mass,
    find_boundary_nodes,
)

# ── fixtures ─────────────────────────────────────────────────


@pytest.fixture
def mock_dag():
    """
    Mock SCC-condensed DAG:

        E ──(depends on)──► A ──► B ──► D
                               │      └──► X
                               └──► C ──► D
                                       └──► Y

    Edge = "source depends on target" = dependencyComponentIds.
    reverseDependentComponentIds is the transpose.
    """
    return {
        "A": {
            "componentId": "A",
            "representative": "a1",
            "dependencyComponentIds": ["B", "C"],
            "reverseDependentComponentIds": ["E"],
            "members": ["a1"],
        },
        "B": {
            "componentId": "B",
            "representative": "b1",
            "dependencyComponentIds": ["D", "X"],
            "reverseDependentComponentIds": ["A"],
            "members": ["b1"],
        },
        "C": {
            "componentId": "C",
            "representative": "c1",
            "dependencyComponentIds": ["D", "Y"],
            "reverseDependentComponentIds": ["A"],
            "members": ["c1"],
        },
        "D": {
            "componentId": "D",
            "representative": "d1",
            "dependencyComponentIds": [],
            "reverseDependentComponentIds": ["B", "C"],
            "members": ["d1"],
        },
        "X": {
            "componentId": "X",
            "representative": "x1",
            "dependencyComponentIds": [],
            "reverseDependentComponentIds": ["B"],
            "members": ["x1"],
        },
        "Y": {
            "componentId": "Y",
            "representative": "y1",
            "dependencyComponentIds": [],
            "reverseDependentComponentIds": ["C"],
            "members": ["y1"],
        },
        "E": {
            "componentId": "E",
            "representative": "e1",
            "dependencyComponentIds": ["A"],
            "reverseDependentComponentIds": [],
            "members": ["e1"],
        },
    }


@pytest.fixture
def mock_tags():
    return {
        "a1": {"name": "a1", "judgment": "capstone_coherence", "depth": "transport",
               "depthNat": 4, "directDepDepthNats": [2, 3]},
        "b1": {"name": "b1", "judgment": "primitive_translator", "depth": "projective",
               "depthNat": 2, "directDepDepthNats": [1]},
        "c1": {"name": "c1", "judgment": "primitive_translator", "depth": "krein",
               "depthNat": 3, "directDepDepthNats": [2]},
        "d1": {"name": "d1", "judgment": "vertical", "depth": "count",
               "depthNat": 1, "directDepDepthNats": []},
        "x1": {"name": "x1", "judgment": "vertical", "depth": "projective",
               "depthNat": 2, "directDepDepthNats": []},
        "y1": {"name": "y1", "judgment": "vertical", "depth": "krein",
               "depthNat": 3, "directDepDepthNats": []},
        "e1": {"name": "e1", "judgment": "capstone_coherence", "depth": "thermo",
               "depthNat": 5, "directDepDepthNats": [4]},
    }


@pytest.fixture
def sig_cache(mock_dag, mock_tags):
    return precompute_signatures(mock_dag, mock_tags)


@pytest.fixture
def own_parity_cache(mock_dag, mock_tags):
    return precompute_own_parities(mock_dag, mock_tags)


# ── BFS / shell tests ───────────────────────────────────────


def test_past_cone_bfs(mock_dag):
    past = past_cone_bfs("A", mock_dag)
    assert past == {"A": 0, "B": 1, "C": 1, "D": 2, "X": 2, "Y": 2}


def test_forward_cone_bfs(mock_dag):
    fwd = forward_cone_bfs("A", mock_dag)
    assert fwd == {"A": 0, "E": 1}


def test_shell_decomposition(mock_dag):
    past = past_cone_bfs("A", mock_dag)
    shells = shell_decomposition(past)
    assert shells[0] == ["A"]
    assert set(shells[1]) == {"B", "C"}
    assert set(shells[2]) == {"D", "X", "Y"}


# ── component signature ─────────────────────────────────────


def test_component_signature(mock_dag, mock_tags):
    depths, parities, judgments = component_signature("A", mock_dag, mock_tags)
    assert depths == {2, 3}
    assert parities == {0, 1}
    assert judgments == {"capstone_coherence"}


def test_component_own_parities(mock_dag, mock_tags):
    """Own parity is derived from depthNat, not directDepDepthNats."""
    # A: depthNat=4 → parity {0}
    assert component_own_parities("A", mock_dag, mock_tags) == {0}
    # B: depthNat=2 → parity {0}
    assert component_own_parities("B", mock_dag, mock_tags) == {0}
    # C: depthNat=3 → parity {1}
    assert component_own_parities("C", mock_dag, mock_tags) == {1}


def test_component_signature_no_deps(mock_dag, mock_tags):
    depths, parities, judgments = component_signature("D", mock_dag, mock_tags)
    assert depths == set()
    assert parities == set()
    assert judgments == {"vertical"}


def test_precompute_signatures(mock_dag, mock_tags, sig_cache):
    assert set(sig_cache.keys()) == set(mock_dag.keys())
    assert sig_cache["A"] == component_signature("A", mock_dag, mock_tags)


# ── binding witnesses ───────────────────────────────────────


def test_find_binding_witnesses(mock_dag, mock_tags, sig_cache):
    past = past_cone_bfs("A", mock_dag)
    witnesses = find_binding_witnesses(past, mock_dag, mock_tags, sig_cache)
    # A: depths {2,3}, parities {0,1}, judgment capstone_coherence → witness
    # B: depths {1}, single class → not a witness
    # C: depths {2}, single class → not a witness
    # D,X,Y: no directDepDepthNats → not witnesses
    assert len(witnesses) == 1
    w = witnesses[0]
    assert w["componentId"] == "A"
    assert w["mixedParity"] is True
    assert set(w["depthClasses"]) == {2, 3}
    assert "capstone_coherence" in w["judgments"]


def test_binding_witnesses_require_coherence(mock_dag, mock_tags, sig_cache):
    """A component with ≥2 depth classes but no coherence role is not a witness."""
    # Give D two depth classes but keep it vertical
    mock_tags["d1"]["directDepDepthNats"] = [0, 1]
    sig_cache_patched = precompute_signatures(mock_dag, mock_tags)
    past = past_cone_bfs("A", mock_dag)
    witnesses = find_binding_witnesses(past, mock_dag, mock_tags, sig_cache_patched)
    witness_cids = {w["componentId"] for w in witnesses}
    assert "D" not in witness_cids
    # restore
    mock_tags["d1"]["directDepDepthNats"] = []


# ── declaration mass ─────────────────────────────────────────


def test_declaration_mass(mock_dag, mock_tags, sig_cache):
    # Forward cone of A: {A:0, E:1}
    # Strict descendants only (dist > 0): {E:1}
    # E: capstone_coherence (w=3), atten=1/(1+1)=0.5, fan_in=1 → 3*0.5/1 = 1.5
    mass, contributors, fwd_size = declaration_mass("A", mock_dag, mock_tags, sig_cache)
    assert fwd_size == 1
    assert contributors == 1
    assert mass == pytest.approx(1.5)


def test_declaration_mass_leaf(mock_dag, mock_tags, sig_cache):
    # Forward cone of D: {D:0, B:1, C:1, A:2, E:3}
    # Strict descendants (dist > 0): {B:1, C:1, A:2, E:3}
    # D: excluded as apex
    # B: primitive_translator (w=2), atten=1/2, fan_in=2 → 2*0.5/2 = 0.5
    # C: primitive_translator (w=2), atten=1/2, fan_in=2 → 2*0.5/2 = 0.5
    # A: capstone_coherence (w=3), atten=1/3, fan_in=2 → 3*(1/3)/2 = 0.5
    # E: capstone_coherence (w=3), atten=1/4, fan_in=1 → 3*0.25/1 = 0.75
    mass, contributors, fwd_size = declaration_mass("D", mock_dag, mock_tags, sig_cache)
    assert fwd_size == 4
    assert contributors == 4
    assert mass == pytest.approx(0.5 + 0.5 + 0.5 + 0.75)


# ── binding mass ─────────────────────────────────────────────


def test_binding_mass(mock_dag, mock_tags, sig_cache, own_parity_cache):
    past = past_cone_bfs("A", mock_dag)
    witnesses = find_binding_witnesses(past, mock_dag, mock_tags, sig_cache)
    # Witness = A, deps in cone: B and C.
    # B own depthNat=2 (even), C own depthNat=3 (odd)
    # even_count=1 (B), odd_count=1 (C)
    # fan_in(A) = 2, synergy = (1*1) / (2*2) = 0.25
    bmass = binding_mass(witnesses, past, mock_dag, mock_tags, own_parity_cache)
    assert bmass == pytest.approx(0.25)


def test_binding_mass_mixed_predecessor(mock_dag, mock_tags):
    """When a component has members with different depthNats spanning both parities,
    it contributes to both even and odd counts."""
    # Add a second member to B with odd depthNat
    mock_dag["B"]["members"] = ["b1", "b2"]
    mock_tags["b2"] = {"name": "b2", "judgment": "primitive_translator", "depth": "krein",
                       "depthNat": 3, "directDepDepthNats": [1]}
    sig_cache_patched = precompute_signatures(mock_dag, mock_tags)
    own_parity_patched = precompute_own_parities(mock_dag, mock_tags)
    past = past_cone_bfs("A", mock_dag)
    witnesses = find_binding_witnesses(past, mock_dag, mock_tags, sig_cache_patched)
    # B own parities: {0 (from b1 depthNat=2), 1 (from b2 depthNat=3)} → both
    # C own parities: {1 (from c1 depthNat=3)} → odd only
    # even_count=1 (B), odd_count=2 (B+C)
    # synergy = (1*2) / (2*2) = 0.5
    bmass = binding_mass(witnesses, past, mock_dag, mock_tags, own_parity_patched)
    assert bmass == pytest.approx(0.5)
    # restore
    mock_dag["B"]["members"] = ["b1"]
    del mock_tags["b2"]


# ── boundary nodes ───────────────────────────────────────────


def test_find_boundary_nodes(mock_dag, mock_tags, sig_cache):
    past = past_cone_bfs("A", mock_dag)
    shells = shell_decomposition(past)
    boundary = find_boundary_nodes("A", shells, past, mock_dag, mock_tags, sig_cache)
    boundary_map = {b["componentId"]: b for b in boundary}

    # Shell 2 (D, X, Y): outermost → boundary
    assert boundary_map["D"]["is_outermost"] is True
    assert boundary_map["X"]["is_outermost"] is True
    assert boundary_map["Y"]["is_outermost"] is True

    # Shell 1 (B, C): reverseDependentComponentIds ∩ past = {A} → desc_in_cone=1
    # That is ≤ 1, so is_low_reuse = True
    assert boundary_map["B"]["is_low_reuse"] is True
    assert boundary_map["C"]["is_low_reuse"] is True

    # Apex is excluded from boundary
    assert "A" not in boundary_map


def test_boundary_nodes_have_coh_support(mock_dag, mock_tags, sig_cache):
    """Every boundary record includes the coh_support field."""
    past = past_cone_bfs("A", mock_dag)
    shells = shell_decomposition(past)
    boundary = find_boundary_nodes("A", shells, past, mock_dag, mock_tags, sig_cache)
    for b in boundary:
        assert "coh_support" in b
        assert isinstance(b["coh_support"], int)


# ── role overlay ─────────────────────────────────────────────


def test_role_overlay_component_granularity(mock_dag, mock_tags, sig_cache):
    past = past_cone_bfs("A", mock_dag)
    shells = shell_decomposition(past)
    overlay = role_overlay(shells, mock_dag, mock_tags)
    # Shell 0: 1 component (A, capstone_coherence)
    assert overlay[0]["size"] == 1
    assert overlay[0]["judgments"].get("capstone_coherence", 0) == 1
    # Shell 1: 2 components (B, C — both primitive_translator)
    assert overlay[1]["size"] == 2
    assert overlay[1]["judgments"].get("primitive_translator", 0) == 2
    # Shell 2: 3 components (D, X, Y — all vertical)
    assert overlay[2]["size"] == 3
    assert overlay[2]["judgments"].get("vertical", 0) == 3
