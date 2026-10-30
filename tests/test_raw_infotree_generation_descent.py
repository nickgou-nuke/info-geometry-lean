"""Generation-scoped descent verification never falls back to legacy rows."""
import pytest
from tools.infra import verify_raw_infotree_arango_descent as descent
from tools.infra.arango_raw_infotree_graph import generation_graph_spec
from tools.infra.arango_raw_infotree_ingest import ROW_FILES, context_edge_collections


def receipt(layout):
    ident = 'b' * 24
    rows = set(ROW_FILES)
    if layout == 'shared':
        rows |= {'raw_infotree_mctx_contexts', 'raw_infotree_lctx_contexts'}
    edges = set(context_edge_collections(layout))
    return {'_key': ident, 'status': 'complete',
            'schema': 'info_geometry.raw_infotree_generation.v1', 'contextLayout': layout,
            'collections': {n: f'{n}_g_{ident}' for n in rows | edges},
            'rowCounts': dict.fromkeys(rows, 0), 'edgeCounts': dict.fromkeys(edges, 0)}


@pytest.mark.parametrize('layout', ['expanded', 'shared'])
def test_queries_are_generation_bound(layout):
    r = receipt(layout)
    _, definitions = generation_graph_spec(r, r['_key'])
    checks = descent.generation_checks(layout, r['collections'], definitions)
    text = '\n'.join(c.query for c in checks)
    assert 'ig_nodes' not in text
    assert '"raw_infotree_nodes/"' not in text
    assert f'raw_infotree_nodes_g_{r["_key"]}/' in text
    if layout == 'shared':
        assert 'raw_infotree_lctx_ref_decl_edges' not in text
        assert 'lctx_shared_sizes_match' in {c.name for c in checks}
        assert 'mctx_refs_exact_context_membership' in {c.name for c in checks}
    assert sum(c.name.endswith('_closed_endpoints') for c in checks) == len(definitions)


@pytest.mark.parametrize('mode', ['valid', 'missing', 'bad_count', 'bad_edge'])
def test_generation_verification_fails_closed(monkeypatch, mode):
    r = receipt('shared')
    monkeypatch.setattr(descent, 'request_json', lambda *a, **k: r)
    existing = set(r['collections'].values())
    if mode == 'missing':
        existing.remove(r['collections']['raw_infotree_nodes'])
    monkeypatch.setattr(descent, 'list_collections', lambda target: existing)
    monkeypatch.setattr(descent, 'collection_count', lambda *a: 1 if mode == 'bad_count' else 0)
    queries = []
    def query(target, text):
        queries.append(text)
        return [{'bad': True}] if mode == 'bad_edge' else []
    monkeypatch.setattr(descent, 'run_aql', query)
    target = descent.ArangoTarget('http://example', 'db', 'root', '')
    result = descent.verify_generation(target, r['_key'])
    assert result['ok'] == (mode == 'valid')
    assert result['external_declaration_join']['status'] == 'not_checked'
    if mode == 'missing':
        assert queries == []


def test_missing_expected_counts_rejected(monkeypatch):
    r = receipt('shared')
    r['rowCounts'].pop('raw_infotree_nodes')
    monkeypatch.setattr(descent, 'request_json', lambda *a, **k: r)
    with pytest.raises(ValueError, match='expected counts'):
        descent.verify_generation(descent.ArangoTarget('', '', '', ''), r['_key'])

@pytest.mark.parametrize('fault', [None, 'provenance', 'row', 'membership'])
def test_context_layout_comparison(monkeypatch, fault):
    old, new = receipt('expanded'), receipt('shared')
    old['_key'] = 'a' * 24
    old['collections'] = {k: v.replace('b' * 24, old['_key']) for k, v in old['collections'].items()}
    for r in (old, new):
        r.update(buildFingerprint='environment', sourceProvenance=[{'sourceSha256': 'source'}])
    if fault == 'provenance':
        new['buildFingerprint'] = 'different'
    monkeypatch.setattr(descent, 'request_json', lambda method, url, **kw:
                        old if url.endswith(old['_key']) else new)
    seen = []
    def query(target, text, bindings):
        seen.append((text, bindings))
        assert 'LIMIT 20' in text
        if fault == 'row' and '@left' in bindings:
            return ['changed']
        if fault == 'membership' and '@expanded' in bindings:
            return [{'reference': 'mismatch'}]
        return []
    monkeypatch.setattr(descent, 'run_aql', query)
    target = descent.ArangoTarget('http://example', 'db', 'root', '')
    if fault == 'provenance':
        with pytest.raises(ValueError, match='provenance mismatch'):
            descent.compare_context_layouts(target, old['_key'], new['_key'])
        assert not seen
    else:
        result = descent.compare_context_layouts(target, old['_key'], new['_key'])
        assert result['ok'] == (fault is None)
        assert len(seen) == 2 * len(ROW_FILES) + 2
