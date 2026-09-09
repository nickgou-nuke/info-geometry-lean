# Branch consolidation audit

This audit was run against every head returned by `git ls-remote --heads upstream`.
The repository currently has 180 upstream heads, including `main`; all pull
requests are already closed. The audit compares each branch's complete tracked
Lean path set with `main`, then inspects branch-only source rather than merging
histories from old bases.

## Disposition

- The repeated 27-file and 28-file groups are historical snapshot material
  absent from the current baseline. Their capstone files are forwarding aliases,
  diagnostics, or depend on rejected/unverified frontiers; they are not promoted.
- The physical logarithmic-braiding branches contain the previously rejected
  physical-braiding frontier. They are not promoted because the current pinned
  Mathlib target does not kernel-check the proposed files and the repository's
  categorical owners remain the truthful boundary.
- The exported G₂ flag-action files are rejected as stale: they assert
  incidence preservation, while `G2ExportedIncidenceGenerator.lean` proves the
  explicit permutations do not preserve incidence. The candidate files also
  fail elaboration against the current owner namespaces.
- The `consolidate/class2` relativity files contain `sorry` proofs and are not
  eligible for `main`.
- Branch-only diagnostics, `#check` files, generated `.olean`/Python artifacts,
  external path sentinels, and backup trees are not source implementations.
- No branch-only file passed the promotion criteria (current owners, complete
  proofs, no debt markers, and kernel-checkable integration). Therefore no
  mathematical gap was promoted from these stale heads.

The valid mathematical content from the closed PRs remains in the canonical
owners already on `main`. Remote branch deletion is performed only after this
classification; `main` is retained as the single integration head.
