# Vacuity Demotion Policy

> Status: `working policy`
> Scope: planner output, mathfulness audit, and hash-equivalence repair routing.
> Rule: fingerprint clusters are evidence for navigation and grouping only, not proof.

This repo does not promote hash-equivalent vacuity surfaces. It demotes them to
repair debt.

## What gets demoted

The planner treats a declaration as repair debt when any of the following hold:

- the mathfulness audit classifies it as `blocked`, `audit_missing`,
  `vacuous_or_surrogate`, `graph_only`, `diagnostic_only`,
  `needs_review_named_bridge`, `kernel_definition`, `explicit_axiom`, or
  `needs_review_external_audit_failed`;
- it shares a normalized fingerprint cluster with a blocked or suspicious
  declaration;
- it appears in a vacuity candidate set and has a hash-equivalent cluster mate
  that already failed admission.

The relevant fingerprint fields are:

- `shapeHash`
- `valueFingerprint`
- `typeFingerprint`

These are normalized by `tools/planner/common.py` and consumed by
`tools/vacuity_planner.py`.

## What the planner emits

The planner now has a dedicated `rankedDemotionQueue`. Each row carries:

- `candidate`
- `demotionAction` = `demote_to_repair`
- `clusterKeys`
- `clusterMembers`
- `blockedAnchors`
- `score`
- `confidence`

This queue is the reverse of promotion. It is a dispatch surface for repair,
not a theorem endorsement surface.

## How to use it

Run the audited gate first:

```bash
python3 tools/quality/mathfulness_audit.py --gate
```

Then generate the planner report:

```bash
python3 tools/vacuity_planner.py \
  --mathfulness-audit reports/dag/mathfulness-audit.json
```

The resulting report is the source of repair triage. It should be used to
dispatch owner-file fixes or subagent proof repair, never to justify a wrapper
or rename-only promotion.

## Policy boundary

- Hashes are navigation evidence, not proof.
- A cluster member does not become acceptable because another member in the
  cluster looks acceptable.
- Wrapper surfaces stay wrappers until the owner theorem is proved.
- The only acceptable end state for a demoted declaration is a kernel-checked
  owner proof or an explicit, bounded debt marker.
