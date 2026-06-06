# Vacuum Candidate Criterion

Audit date: 2026-06-06.

This criterion is for redundancy cleanup in `info-geometry-lean`.

```text
vacuum candidate =
  graph-current present
  proof-processing absent
  protected harmonic intersection empty
  Lean owner equivalent exists
```

## Meaning

### Graph-current present

The declaration or module is visible to the graph layer as a real wire:

- it appears in the Lean DAG / LeanTrail snapshot;
- it has dependency or import flow;
- it lies in a WL/hash/duplicate/conductance/process-flow lane worth inspecting.

Graph-current alone never proves vacuity. It only says there is a wire to audit.

### Proof-processing absent

The source does not materially process mathematical content. Typical evidence:

- pure forwarding to another declaration;
- projection/readback from a witness packet;
- compatibility alias with no remaining independent role;
- theorem wrapper around an owner theorem;
- proof by generic logic where domain constants are unused;
- statement/proof pair that packages assumptions but proves no new invariant.

### Protected harmonic intersection empty

The candidate has no protected owner content in the Hodge/chiral decomposition:

- no categorical owner surface;
- no API/protected theorem intersection;
- no harmonic representative carrying independent theory;
- no capstone or owner declaration that downstream files intentionally depend on.

If harmonic/protected content is present, the candidate is not vacuum. It may be
a bridge, owner theorem, or protected boundary artifact.

### Lean owner equivalent exists

There is a kernel-checked declaration or module that already owns the content.
The proposed contraction must point to that owner and preserve behavior under a
targeted Lean build.

## Required Dossier

Before any contraction, record:

```text
candidate:
  name/module:
  graph evidence:
  source evidence:
  protected/harmonic intersection:
  Lean owner equivalent:
  proposed contraction:
  validation target:
```

Reject the contraction if any field is missing.

## Hard Rule

```text
Graph/Hodge/chiral operators identify vacuum candidates.
Lean owner files decide truth.
Only kernel-checked edits count.
```

Do not delete, rewrite, or collapse a declaration solely because it is isolated,
low-conductance, hash-duplicated, or graph-centrality weak.
