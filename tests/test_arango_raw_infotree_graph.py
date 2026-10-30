"""Generation-isolated graph definitions and fail-closed reuse."""
import pytest
from tools.infra import arango_raw_infotree_graph as graph
from tools.infra.arango_raw_infotree_ingest import ROW_FILES, context_edge_collections


@pytest.mark.parametrize('layout', ['expanded', 'shared'])
def test_generation_graph_covers_all_rows_and_edges(layout):
    generation = 'a' * 24
    names = set(ROW_FILES) | set(context_edge_collections(layout))
    if layout == 'shared':
        names |= {'raw_infotree_mctx_contexts', 'raw_infotree_lctx_contexts'}
    receipt = {'_key': generation, 'status': 'complete',
               'schema': 'info_geometry.raw_infotree_generation.v1',
               'contextLayout': layout,
               'collections': {n: f'{n}_g_{generation}' for n in names}}
    actual_layout, definitions = graph.generation_graph_spec(receipt, generation)
    assert actual_layout == layout
    assert {d['collection'] for d in definitions} == {
        f'{n}_g_{generation}' for n in context_edge_collections(layout)}
    vertices = {n for d in definitions for n in d['from'] + d['to']}
    assert vertices == {f'{n}_g_{generation}' for n in names - set(context_edge_collections(layout))}
    receipt['collections']['raw_infotree_nodes'] = 'raw_infotree_nodes'
    with pytest.raises(ValueError, match='collection map'):
        graph.generation_graph_spec(receipt, generation)


def test_existing_graph_mismatch_is_rejected_without_mutation(monkeypatch):
    calls = []
    monkeypatch.setattr(graph, 'graph_exists', lambda *args: True)
    def request(method, *args, **kwargs):
        calls.append(method)
        return {'graph': {'edgeDefinitions': [], 'orphanCollections': []}}
    monkeypatch.setattr(graph, 'request_json', request)
    target = graph.ArangoTarget('http://example', 'db', 'user', '')
    with pytest.raises(ValueError, match='differs'):
        graph.create_graph(target, 'existing', replace=False)
    assert calls == ['GET']


def test_existing_matching_graph_is_reused(monkeypatch):
    monkeypatch.setattr(graph, 'graph_exists', lambda *args: True)
    monkeypatch.setattr(graph, 'request_json', lambda *a, **k: {
        'graph': {'edgeDefinitions': list(reversed(graph.graph_definitions())), 'orphanCollections': []}})
    target = graph.ArangoTarget('http://example', 'db', 'user', '')
    assert graph.create_graph(target, 'existing', replace=False)['created'] is False
