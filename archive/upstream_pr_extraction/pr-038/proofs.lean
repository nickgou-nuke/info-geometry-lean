/-!
Root module for the `proofs` library.

The proofs previously lived under `external_refs/auto/proofs` as a separate
Lake root (its own mathlib checkout and build hash). They are now part of this
repository and compile against the single shared `.lake/packages/mathlib`
under this project's one build hash — no second mathlib, no cache thrash.
-/
