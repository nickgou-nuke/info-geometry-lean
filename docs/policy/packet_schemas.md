# Spire Packet Schemas

> Status: `reference memory`
> Audited: 2026-05-02
> Note: Re-audit against current code before using for policy, design claims, or status.
> See: [README.md](../../README.md), [docs/README.md](../README.md), [docs/CODEBASE_STATUS.md](../CODEBASE_STATUS.md)

These schemas define the strict JSON handshakes between the Proposer and Formalizer agents. They ensure that the formalization process is deterministic, auditable, and grounded in the repository's bedrock.

## I. Chain of States (Symbolic Decomposition)
The Proposer emits a list of `ChainOfStates` objects to decompose the informal proof logic.

```json
{
  "chainId": "string (uuid or task_id_vN)",
  "states": [
    {
      "state_id": "integer",
      "source_prose": "string (informal step description)",
      "formal_target": "string (intended Lean tactic or term state)",
      "target_kind": "enum [def, lemma, theorem, helper]",
      "expected_owner_namespace": "string (e.g., InfoGeometry.Canonical)",
      "candidate_premises": ["string (suggested constant names)"],
      "blocked_by": ["integer (state dependencies)"],
      "discharge_status": "enum [pending, verified, failed]"
    }
  ]
}
```

## II. Premise Packet (Fact Substrate)
The Retriever attaches a `PremisePacket` to each state (or the task as a whole) to provide the factual context for formalization.

```json
{
  "exact_theorem_target": "string (signature name)",
  "current_imports": ["string (baseline imports)"],
  "local_declarations": [
    {
      "name": "string",
      "type": "string",
      "docstring": "string"
    }
  ],
  "canonical_repo_lemmas": ["string"],
  "mathlib_candidates": ["string"],
  "disallowed_premises": ["string (forbidden by manifest/policy)"],
  "dependency_budget": {
    "max_new_imports": "integer",
    "allowed_witnesses": ["string"]
  },
  "rep_depth_tags": ["string (L1, L2, L3 markers)"]
}
```

## III. Protocol Rules
1.  **Immutability**: Once a `ChainOfStates` is accepted by the Formalizer, its `formal_target` signatures are locked.
2.  **Exclusion**: Any tactic used by the Formalizer that relies on a premise in `disallowed_premises` will trigger an automatic audit failure.
3.  **Traceability**: Every generated proof term must cite the `state_id` from which it was derived.
