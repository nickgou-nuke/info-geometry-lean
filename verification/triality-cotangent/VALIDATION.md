# Validation record

## Initial candidate checkpoint

- Base: `fe24e350b08fdea04f74c0748ef9fd9417c47529` (`main`).
- Lean pin: `leanprover/lean4:v4.34.1`.
- Mathlib pin: `d13f23b723b8a846827a245b89c10fc7d3f11612`.
- Canonical sources are pending kernel validation at this checkpoint.
- The initial local check waited for the maintained shared build lock, held
  by another task. The waiting request was cancelled before acquiring the
  lock or starting Lean/Lake; no competing compiler process was stopped.
- The dedicated GitHub workflow is the remote kernel-validation route.
- A mathematical challenger independently checked the groupoid semantics,
  Reynolds dual equivalence, shear counterexample, coordinate conjugacy and
  faithful finite action. Its review is not a compilation result.
- The extracted Cartan declaration block is byte-for-byte equal to the
  original block; the existing consumer is a separate regression target.

Results will be appended with the exact workflow/head, exit results,
declaration inventory, foundational axioms, and remaining boundaries.
