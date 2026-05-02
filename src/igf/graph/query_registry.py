"""Canonical AQL query registry for igf greenfield kernel.

All operational queries should be referenced by ID and tested via contract fixtures.
"""

from __future__ import annotations

from dataclasses import dataclass
from typing import Dict


@dataclass(frozen=True)
class QuerySpec:
    id: str
    description: str
    aql: str


QUERIES: Dict[str, QuerySpec] = {
    "verify.run_summary": QuerySpec(
        id="verify.run_summary",
        description="Run-scoped counts for patches/spectral/members/edges",
        aql="""
LET runId = @run_id
LET patchKeys = (FOR p IN ig_chiral_patches FILTER p.run_id == runId RETURN p._key)
LET pcount = LENGTH(patchKeys)
LET scount = LENGTH(FOR s IN ig_patch_spectral_signatures FILTER s.run_id == runId AND s.patch_id IN patchKeys RETURN 1)
LET mcount = LENGTH(FOR m IN ig_patch_members FILTER NOT_NULL(m.run_id, m.patch_run_id) == runId AND PARSE_IDENTIFIER(m._from).key IN patchKeys RETURN 1)
LET ecount = LENGTH(FOR e IN ig_patch_edges FILTER NOT_NULL(e.run_id, e.patch_run_id) == runId AND PARSE_IDENTIFIER(e._from).key IN patchKeys RETURN 1)
RETURN {run_id: runId, patches: pcount, spectral: scount, members: mcount, patch_edges: ecount}
""".strip(),
    ),
    "verify.latest_run_id": QuerySpec(
        id="verify.latest_run_id",
        description="Resolve latest canonical run_id from run docs",
        aql="""
RETURN FIRST(FOR r IN ig_patch_runs SORT r.created_at DESC LIMIT 1 RETURN r.run_id)
""".strip(),
    ),
    "verify.orphan_spectral": QuerySpec(
        id="verify.orphan_spectral",
        description="Spectral rows whose patch_id is missing in same run",
        aql="""
FOR s IN ig_patch_spectral_signatures
  LET p = FIRST(
    FOR x IN ig_chiral_patches
      FILTER x.run_id == s.run_id AND x.patch_id == s.patch_id
      LIMIT 1 RETURN x
  )
  FILTER p == null
  RETURN {run_id: s.run_id, patch_id: s.patch_id, spectral_key: s._key}
""".strip(),
    ),
    "verify.orphan_members": QuerySpec(
        id="verify.orphan_members",
        description="Member edges whose _from patch node is missing",
        aql="""
FOR m IN ig_patch_members
  LET runId = NOT_NULL(m.run_id, m.patch_run_id)
  LET pid = PARSE_IDENTIFIER(m._from).key
  LET p = DOCUMENT(CONCAT('ig_chiral_patches/', pid))
  FILTER p == null OR p.run_id != runId
  RETURN {run_id: runId, patch_key: pid, to: m._to}
""".strip(),
    ),
    "verify.orphan_patch_edges": QuerySpec(
        id="verify.orphan_patch_edges",
        description="Patch edges whose source/target patch is missing",
        aql="""
FOR e IN ig_patch_edges
  LET runId = NOT_NULL(e.run_id, e.patch_run_id)
  LET fromKey = PARSE_IDENTIFIER(e._from).key
  LET toKey = PARSE_IDENTIFIER(e._to).key
  LET fromDoc = DOCUMENT(CONCAT('ig_chiral_patches/', fromKey))
  LET toDoc = DOCUMENT(CONCAT('ig_chiral_patches/', toKey))
  FILTER fromDoc == null OR toDoc == null OR fromDoc.run_id != runId OR toDoc.run_id != runId
  RETURN {run_id: runId, from_key: fromKey, to_key: toKey}
""".strip(),
    ),
}


def get_query(query_id: str) -> QuerySpec:
    try:
        return QUERIES[query_id]
    except KeyError as exc:
        raise KeyError(f"Unknown query id: {query_id}") from exc
