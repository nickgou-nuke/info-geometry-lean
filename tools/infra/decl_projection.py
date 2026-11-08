"""Generation-pinned PostgreSQL declaration and dependency projection store.

No environment reads, connections, migration execution or CLI side effects.
Use a dedicated idle psycopg3 connection with autocommit=True and tuple rows.
Each write method owns exactly one transaction. Public semantic rows are anchors,
never the evidence that a declaration/edge belongs to a generation.
"""
from __future__ import annotations

from dataclasses import dataclass
import hashlib
import json
from pathlib import Path
import re
import sys
from typing import Iterable
from uuid import UUID, uuid4

_REPO_ROOT = Path(__file__).resolve().parents[2]
for _p in (_REPO_ROOT / "src", _REPO_ROOT):
    if str(_p) not in sys.path:
        sys.path.insert(0, str(_p))

from igf.graph.decl_schema import decl_key, edge_key
try:
    from tools.infra.decl_graph_generation import (
        validate_generation_counts, validate_generation_id, validate_generation_metadata,
    )
except ImportError:
    from decl_graph_generation import (
        validate_generation_counts, validate_generation_id, validate_generation_metadata,
    )


def _import_psycopg_pq():
    try:
        from psycopg.pq import TransactionStatus
        return TransactionStatus
    except ImportError:
        return None


def _import_psycopg_json():
    try:
        from psycopg.types.json import Jsonb
        return Jsonb
    except ImportError:
        return None

DIGEST_VERSION = 'ig-decl-projection-v1'
DEFAULT_DEPLOYMENT_UUID = UUID('00000000-0000-4000-8000-000000000001')


class ProjectionConflict(ValueError):
    pass


@dataclass(frozen=True)
class Source:
    deployment_uuid: UUID
    arango_database: str

    def __post_init__(self):
        if not isinstance(self.deployment_uuid, UUID) or self.deployment_uuid.int == 0:
            raise ValueError('supply a provisioned, stable, nonzero deployment UUID')
        if not isinstance(self.arango_database, str) or not self.arango_database.strip():
            raise ValueError('explicit Arango database is required')


@dataclass(frozen=True)
class Selection:
    generation: UUID | None
    revision: int


@dataclass(frozen=True)
class Snapshot:
    generation: UUID
    revision: int
    receipt: dict
    digest: str


def _json_domain(value):
    # Deliberately exclude floats: Python/JSONB numeric round trips must not alter
    # the digest. Current compiler payloads use strings, integers, booleans/null.
    if value is None or isinstance(value, (str, bool, int)):
        return
    if isinstance(value, list):
        for item in value:
            _json_domain(item)
        return
    if isinstance(value, dict) and all(isinstance(k, str) for k in value):
        for item in value.values():
            _json_domain(item)
        return
    raise ValueError('payload must use string-key JSON objects, arrays and non-float primitives')


def _frame(hasher, value):
    _json_domain(value)
    encoded = json.dumps(value, ensure_ascii=True, sort_keys=True,
                         separators=(',', ':'), allow_nan=False).encode('ascii')
    hasher.update(len(encoded).to_bytes(8, 'big'))
    hasher.update(encoded)


def source_digest(source: Source, receipt: dict, declarations: Iterable, edges: Iterable) -> str:
    """Compute on independently read SOURCE rows before begin_generation.

    declarations: sorted (key, name, module, raw_payload) tuples.
    edges: sorted (key, src_key, dst_key, kind, raw_payload) tuples.
    Sort by key UTF-8 bytes, matching PostgreSQL COLLATE "C" in a UTF8 database.
    Metadata and all payload fields participate; local term/catalog IDs do not.
    Framing/tagging prevents concatenation, record-type and boundary ambiguity.
    """
    digest = hashlib.sha256()
    _frame(digest, [DIGEST_VERSION, str(source.deployment_uuid), source.arango_database, receipt])
    for tag, records in (('declaration', declarations), ('dependency', edges)):
        previous = None
        for row in records:
            key = row[0].encode('utf-8')
            if previous is not None and key <= previous:
                raise ValueError('digest rows must have strictly increasing keys')
            previous = key
            _frame(digest, [tag, *row])
    return digest.hexdigest()


class ProjectionStore:
    def __init__(self, connection):
        self.conn = connection

    def _idle(self):
        if not self.conn.autocommit or self.conn.info.transaction_status != _import_psycopg_pq().IDLE:
            raise ValueError('use dedicated idle autocommit connection; nested transactions prohibited')

    @staticmethod
    def _loading(cur, generation):
        cur.execute('SELECT status FROM ig_decl_projection.generation WHERE id=%s FOR UPDATE',
                    (generation,))
        row = cur.fetchone()
        if row != ('loading',):
            raise ProjectionConflict('generation absent or no longer loading')

    def register_source(self, source: Source, catalog_database_id: str):
        """Register explicit existing catalog anchor. No endpoint-derived identity."""
        self._idle()
        with self.conn.transaction(), self.conn.cursor() as cur:
            cur.execute('INSERT INTO ig_decl_projection.source VALUES (%s,%s,%s) '
                        'ON CONFLICT (deployment_uuid,arango_database) DO NOTHING',
                        (source.deployment_uuid, source.arango_database, catalog_database_id))
            cur.execute('SELECT catalog_database_id FROM ig_decl_projection.source '
                        'WHERE deployment_uuid=%s AND arango_database=%s',
                        (source.deployment_uuid, source.arango_database))
            if cur.fetchone() != (catalog_database_id,):
                raise ProjectionConflict('source already bound to another catalog')

    def current_selection(self, source: Source, import_root: str, namespace: str) -> Selection:
        """Read current (selected_generation, revision) for scope, or Selection(None, 0)."""
        self._idle()
        with self.conn.cursor() as cur:
            cur.execute(
                'SELECT selected_generation, revision FROM ig_decl_projection.scope_selection '
                'WHERE deployment_uuid=%s AND arango_database=%s AND import_root=%s AND namespace=%s',
                (source.deployment_uuid, source.arango_database, import_root, namespace),
            )
            row = cur.fetchone()
            if row is None:
                return Selection(None, 0)
            return Selection(row[0], row[1])

    def find_generation(self, source: Source, generation_id: str) -> tuple[UUID, str, str | None] | None:
        """Return (id, status, actual_digest) if (source, generation_id) exists."""
        self._idle()
        with self.conn.cursor() as cur:
            cur.execute(
                'SELECT id, status, actual_digest FROM ig_decl_projection.generation '
                'WHERE deployment_uuid=%s AND arango_database=%s AND generation_id=%s',
                (source.deployment_uuid, source.arango_database, generation_id),
            )
            return cur.fetchone()

    def begin_generation(self, source: Source, generation_id: str, receipt: dict,
                         expected_digest: str) -> UUID:
        """Strict create; duplicate source+generation is an error, never an overwrite.

        Caller supplies a freshly validated Arango receipt AND independent source
        digest. This API cannot authenticate caller-supplied source evidence.
        """
        validate_generation_id(generation_id)
        if (receipt.get('_key') != generation_id or receipt.get('status') != 'complete'
                or receipt.get('schema') != 'info_geometry.decl_graph_generation.v1'):
            raise ValueError('receipt identity/schema/status mismatch')
        validate_generation_metadata(receipt.get('buildFingerprint'), receipt.get('importRoot'),
                                     receipt.get('namespace'))
        validate_generation_counts(receipt.get('declarationCount'), receipt.get('emittedEdgeCount'),
                                   receipt.get('validEdgeCount'), receipt.get('removedOrphanCount'))
        for field in ('declCollection', 'edgeCollection'):
            if not isinstance(receipt.get(field), str) or not re.fullmatch(r'[A-Za-z0-9_]+', receipt[field]):
                raise ValueError('invalid receipt collection')
        if not isinstance(expected_digest, str) or not re.fullmatch(r'[0-9a-f]{64}', expected_digest):
            raise ValueError('independent expected SHA-256 digest is required')
        _json_domain(receipt)
        self._idle()
        generation = uuid4()
        with self.conn.transaction(), self.conn.cursor() as cur:
            cur.execute('''INSERT INTO ig_decl_projection.generation
                (id,deployment_uuid,arango_database,generation_id,import_root,namespace,
                 build_fingerprint,receipt,expected_declarations,expected_edges,
                 digest_version,expected_digest)
                VALUES (%s,%s,%s,%s,%s,%s,%s,%s,%s,%s,%s,%s)''',
                (generation, source.deployment_uuid, source.arango_database, generation_id,
                 receipt['importRoot'], receipt['namespace'], receipt['buildFingerprint'],
                 _import_psycopg_json()(receipt), receipt['declarationCount'], receipt['validEdgeCount'],
                 DIGEST_VERSION, expected_digest))
        return generation

    def append_declarations(self, generation: UUID, rows: Iterable[tuple[dict, str, str]]):
        """Each tuple: unchanged source document, explicit term_id, module table_id.

        All declaration batches precede edge batches. No ON CONFLICT: repeated
        rows reject the entire batch; caller must resolve uncertain commits.
        """
        self._idle()
        with self.conn.transaction(), self.conn.cursor() as cur:
            self._loading(cur, generation)
            with cur.copy('COPY ig_decl_projection.declaration '
                          '(generation,decl_key,name,module,payload,term_id,catalog_table_id) FROM STDIN') as cp:
                for payload, term_id, table_id in rows:
                    _json_domain(payload)
                    if not isinstance(payload, dict):
                        raise ValueError('declaration must be an object')
                    key, name, module = (payload.get(k) for k in ('_key', 'name', 'module'))
                    if any(not isinstance(v, str) or not v.strip() for v in (key, name, module)):
                        raise ValueError('declaration identity/module required')
                    if key != decl_key(name) or payload.get('key', key) != key:
                        raise ValueError('declaration key/name mismatch')
                    cp.write_row((generation, key, name, module, _import_psycopg_json()(payload), term_id, table_id))

    def append_dependencies(self, generation: UUID, payloads: Iterable[dict]):
        self._idle()
        with self.conn.transaction(), self.conn.cursor() as cur:
            self._loading(cur, generation)
            cur.execute('SELECT receipt FROM ig_decl_projection.generation WHERE id=%s', (generation,))
            collection = cur.fetchone()[0]['declCollection']
            with cur.copy('COPY ig_decl_projection.dependency '
                          '(generation,edge_key,src_key,dst_key,kind,payload) FROM STDIN') as cp:
                for payload in payloads:
                    _json_domain(payload)
                    if not isinstance(payload, dict):
                        raise ValueError('edge must be an object')
                    key, src, dst, kind = (payload.get(k) for k in ('_key', 'src', 'dst', 'kind'))
                    if any(not isinstance(v, str) or not v for v in (key, src, dst)):
                        raise ValueError('named edge identity required')
                    if kind not in ('type', 'value') or key != edge_key(src, kind, dst):
                        raise ValueError('edge key/kind mismatch')
                    src_key, dst_key = decl_key(src), decl_key(dst)
                    for field, target in (('_from', src_key), ('_to', dst_key)):
                        if payload.get(field) != f'{collection}/{target}':
                            raise ValueError('edge must address exact generation declaration collection')
                    cp.write_row((generation, key, src_key, dst_key, kind, _import_psycopg_json()(payload)))

    def _rows(self, query, params):
        # Named cursors bound memory for millions of graph rows. Call only inside
        # complete transaction, which retains the generation lock throughout.
        with self.conn.cursor(name='projection_' + uuid4().hex) as cur:
            cur.itersize = 5000
            cur.execute(query, params)
            yield from cur

    @staticmethod
    def _reconcile_public_tables(cur, deployment: UUID, database: str, generation: UUID):
        """Synchronize public.table__term and public.term__term to the active generation."""
        cur.execute(
            '''DELETE FROM public.table__term tt
               USING public.catalog_table ct, public.catalog_schema cs, ig_decl_projection.source s
               WHERE tt.table_id = ct.id
                 AND ct.schema_id = cs.id
                 AND cs.database_id = s.catalog_database_id
                 AND s.deployment_uuid = %s
                 AND s.arango_database = %s
                 AND NOT EXISTS (
                     SELECT 1 FROM ig_decl_projection.declaration d
                     WHERE d.generation = %s
                       AND d.catalog_table_id = tt.table_id
                       AND d.term_id = tt.term_id
                 )''',
            (deployment, database, generation),
        )
        cur.execute(
            '''INSERT INTO public.table__term (table_id, term_id)
               SELECT d.catalog_table_id, d.term_id
               FROM ig_decl_projection.declaration d
               WHERE d.generation = %s
               ON CONFLICT DO NOTHING''',
            (generation,),
        )
        cur.execute(
            '''DELETE FROM public.term__term tt
               WHERE NOT EXISTS (
                   SELECT 1
                   FROM ig_decl_projection.dependency e
                   JOIN ig_decl_projection.declaration src_d
                     ON src_d.generation = e.generation AND src_d.decl_key = e.src_key
                   JOIN ig_decl_projection.declaration dst_d
                     ON dst_d.generation = e.generation AND dst_d.decl_key = e.dst_key
                   WHERE e.generation = %s
                     AND src_d.term_id = tt.src_term_id
                     AND dst_d.term_id = tt.dst_term_id
                     AND e.kind = tt.kind
               )''',
            (generation,),
        )
        cur.execute(
            '''INSERT INTO public.term__term (src_term_id, dst_term_id, kind, created_at)
               SELECT src_d.term_id, dst_d.term_id, e.kind, now()
               FROM ig_decl_projection.dependency e
               JOIN ig_decl_projection.declaration src_d
                 ON src_d.generation = e.generation AND src_d.decl_key = e.src_key
               JOIN ig_decl_projection.declaration dst_d
                 ON dst_d.generation = e.generation AND dst_d.decl_key = e.dst_key
               WHERE e.generation = %s
               ON CONFLICT (src_term_id, dst_term_id, kind) DO NOTHING''',
            (generation,),
        )

    def complete_and_select(
        self,
        generation: UUID,
        expected: Selection,
        *,
        reconcile_public: bool = False,
    ) -> Selection:
        """Validate frozen rows, then complete and CAS-select in ONE transaction.

        If predecessor/revision is stale, every mutation in this call rolls back;
        committed loading batches remain available for diagnosis. No auto-retry.
        """
        if (not isinstance(expected.revision, int) or isinstance(expected.revision, bool)
                or expected.revision < 0):
            raise ValueError('invalid expected selection revision')
        self._idle()
        with self.conn.transaction(), self.conn.cursor() as cur:
            # Generation identity columns never change. Scope is locked before
            # generation; appenders lock only generation, avoiding reverse order.
            cur.execute('''SELECT deployment_uuid,arango_database,import_root,namespace,
                           receipt,expected_declarations,expected_edges,expected_digest
                           FROM ig_decl_projection.generation WHERE id=%s''', (generation,))
            row = cur.fetchone()
            if row is None:
                raise ProjectionConflict('unknown generation')
            deployment, database, root, namespace, receipt, ndeclarations, nedges, expected_digest = row
            scope = (deployment, database, root, namespace)
            cur.execute('''INSERT INTO ig_decl_projection.scope_selection
                (deployment_uuid,arango_database,import_root,namespace) VALUES (%s,%s,%s,%s)
                ON CONFLICT DO NOTHING''', scope)
            cur.execute('''SELECT selected_generation,revision FROM ig_decl_projection.scope_selection
                WHERE deployment_uuid=%s AND arango_database=%s AND import_root=%s AND namespace=%s
                FOR UPDATE''', scope)
            if cur.fetchone() != (expected.generation, expected.revision):
                raise ProjectionConflict('selection predecessor/revision changed')
            self._loading(cur, generation)
            cur.execute('''SELECT (SELECT count(*) FROM ig_decl_projection.declaration WHERE generation=%s),
                                  (SELECT count(*) FROM ig_decl_projection.dependency WHERE generation=%s)''',
                        (generation, generation))
            if cur.fetchone() != (ndeclarations, nedges):
                raise ProjectionConflict('stored counts disagree with source receipt')
            # Validate explicit anchors, not global table__term/term__term membership.
            # SHARE locks prevent anchor identity changes until publication commits.
            mapping_query = '''SELECT d.name,d.decl_key,d.module,t.name,t.imported_id,t.source,
                                      ct.name,cs.database_id,s.catalog_database_id
                FROM ig_decl_projection.declaration d
                JOIN public.term t ON t.id=d.term_id
                JOIN public.catalog_table ct ON ct.id=d.catalog_table_id
                JOIN public.catalog_schema cs ON cs.id=ct.schema_id
                JOIN ig_decl_projection.source s ON s.deployment_uuid=%s AND s.arango_database=%s
                WHERE d.generation=%s FOR SHARE OF t,ct,cs'''
            mapped = 0
            for name, key, module, tname, imported, source, table, db_id, anchor in self._rows(
                    mapping_query, (deployment, database, generation)):
                if (name, key, 'semantic', module, anchor) != (tname, imported, source, table, db_id):
                    raise ProjectionConflict('term/module anchor mapping mismatch')
                mapped += 1
            if mapped != ndeclarations:
                raise ProjectionConflict('incomplete explicit mappings')
            digest = source_digest(Source(deployment, database), receipt,
                self._rows('''SELECT decl_key,name,module,payload FROM ig_decl_projection.declaration
                              WHERE generation=%s ORDER BY decl_key COLLATE "C"''', (generation,)),
                self._rows('''SELECT edge_key,src_key,dst_key,kind,payload FROM ig_decl_projection.dependency
                              WHERE generation=%s ORDER BY edge_key COLLATE "C"''', (generation,)))
            if digest != expected_digest:
                raise ProjectionConflict('projection payload digest differs from source')
            if reconcile_public:
                self._reconcile_public_tables(cur, deployment, database, generation)
            cur.execute('''UPDATE ig_decl_projection.generation SET status='complete',
                actual_digest=%s,completed_at=now() WHERE id=%s AND status='loading' ''', (digest, generation))
            if cur.rowcount != 1:
                raise ProjectionConflict('completion state changed')
            cur.execute('''UPDATE ig_decl_projection.scope_selection
                SET selected_generation=%s,revision=revision+1
                WHERE deployment_uuid=%s AND arango_database=%s AND import_root=%s AND namespace=%s
                  AND selected_generation IS NOT DISTINCT FROM %s AND revision=%s''',
                (generation, *scope, expected.generation, expected.revision))
            if cur.rowcount != 1:
                raise ProjectionConflict('selection compare-and-swap failed')
        return Selection(generation, expected.revision + 1)

    def resolve_snapshot(self, source: Source, import_root: str, namespace: str) -> Snapshot:
        """Resolve selection exactly once. All subsequent pages use this UUID."""
        self._idle()
        with self.conn.cursor() as cur:
            cur.execute('''SELECT g.id,s.revision,g.receipt,g.actual_digest
                FROM ig_decl_projection.scope_selection s
                JOIN ig_decl_projection.generation g ON g.id=s.selected_generation
                WHERE s.deployment_uuid=%s AND s.arango_database=%s AND s.import_root=%s
                    AND s.namespace=%s AND g.status='complete' ''',
                (source.deployment_uuid, source.arango_database, import_root, namespace))
            row = cur.fetchone()
        if row is None:
            raise ProjectionConflict('no complete selected snapshot for explicit scope')
        return Snapshot(*row)

    def declaration_page(self, snapshot: Snapshot, after: str = '', limit: int = 1000):
        return self._page(snapshot, after, limit, edges=False)

    def dependency_page(self, snapshot: Snapshot, after: str = '', limit: int = 1000):
        return self._page(snapshot, after, limit, edges=True)

    def _page(self, snapshot, after, limit, *, edges):
        if isinstance(limit, bool) or not isinstance(limit, int) or not 1 <= limit <= 10000:
            raise ValueError('page limit must be 1..10000')
        self._idle()
        # SQL fragments are constants, never caller-supplied identifiers.
        table, key, fields = (('dependency', 'edge_key', 'm.edge_key,m.src_key,m.dst_key,m.kind,m.payload')
                              if edges else ('declaration', 'decl_key',
                                             'm.decl_key,m.name,m.module,m.payload,m.term_id,m.catalog_table_id'))
        with self.conn.cursor() as cur:
            cur.execute(f'''SELECT {fields} FROM ig_decl_projection.{table} m
                JOIN ig_decl_projection.generation g ON g.id=m.generation AND g.status='complete'
                WHERE m.generation=%s AND m.{key} COLLATE "C" > %s COLLATE "C"
                ORDER BY m.{key} COLLATE "C" LIMIT %s''', (snapshot.generation, after, limit))
            return cur.fetchall()
