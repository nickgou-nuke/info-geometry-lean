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
        description="Run-scoped counts for patches/spectral/members/edges using run_id joins",
        aql="""
LET runId = @run_id
LET patchIds = (FOR p IN ig_chiral_patches FILTER p.run_id == runId RETURN p.patch_id)
LET pcount = LENGTH(patchIds)
LET scount = LENGTH(FOR s IN ig_patch_spectral_signatures FILTER s.run_id == runId AND s.patch_id IN patchIds RETURN 1)
LET mcount = LENGTH(FOR m IN ig_patch_members FILTER m.run_id == runId AND m.patch_id IN patchIds RETURN 1)
LET ecount = LENGTH(FOR e IN ig_patch_edges FILTER e.run_id == runId AND e.from_patch_id IN patchIds AND e.to_patch_id IN patchIds RETURN 1)
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
  FILTER s.run_id == @run_id
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
  FILTER m.run_id == @run_id
  LET p = FIRST(
    FOR x IN ig_chiral_patches
      FILTER x.run_id == m.run_id AND x.patch_id == m.patch_id
      LIMIT 1 RETURN x
  )
  FILTER p == null
  RETURN {run_id: m.run_id, patch_id: m.patch_id, to: m._to}
""".strip(),
    ),
    "verify.orphan_patch_edges": QuerySpec(
        id="verify.orphan_patch_edges",
        description="Patch edges whose source/target patch is missing",
        aql="""
FOR e IN ig_patch_edges
  FILTER e.run_id == @run_id
  LET fromDoc = FIRST(
    FOR p IN ig_chiral_patches
      FILTER p.run_id == e.run_id AND p.patch_id == e.from_patch_id
      LIMIT 1 RETURN p
  )
  LET toDoc = FIRST(
    FOR p IN ig_chiral_patches
      FILTER p.run_id == e.run_id AND p.patch_id == e.to_patch_id
      LIMIT 1 RETURN p
  )
  FILTER fromDoc == null OR toDoc == null
  RETURN {run_id: e.run_id, from_patch_id: e.from_patch_id, to_patch_id: e.to_patch_id}
""".strip(),
    ),
    "verify.policy_violations": QuerySpec(
        id="verify.policy_violations",
        description="Patch sidecar rows with missing or over-claiming policy fields",
        aql="""
LET runId = @run_id
FOR doc IN UNION(
  (FOR p IN ig_chiral_patches FILTER p.run_id == runId RETURN MERGE(p, {collection: 'ig_chiral_patches'})),
  (FOR s IN ig_patch_spectral_signatures FILTER s.run_id == runId RETURN MERGE(s, {collection: 'ig_patch_spectral_signatures'}))
)
  FILTER doc.non_overclaim != true
     OR doc.claim_scope == null
     OR doc.authority_level == null
     OR (doc.authority_level == 'formal' AND doc.proof_link == null)
  RETURN KEEP(doc, '_key', 'patch_id', 'run_id', 'collection', 'authority_level', 'claim_scope', 'non_overclaim', 'proof_link')
""".strip(),
    ),
}


def get_query(query_id: str) -> QuerySpec:
    try:
        return QUERIES[query_id]
    except KeyError as exc:
        raise KeyError(f"Unknown query id: {query_id}") from exc
