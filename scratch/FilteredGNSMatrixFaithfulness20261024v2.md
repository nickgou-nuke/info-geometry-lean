# Matrix GNS faithfulness v2 — local instance repair

Uncompiled candidate; all five v1 theorem statements and imports unchanged.
V1 and its contract are preserved. Mathematical contract and source mapping:
`FilteredGNSMatrixFaithfulness20261024.md`.

QA source: `/tmp/qa-a-filteredgnsmatrixfaithfulness20261024-s8pp6hcb/compile.log`.
The only Lean error reported is the default 20000-heartbeat typeclass timeout
for bounded-endomorphism Nontrivial at v1 line 42. Dependency dirty warnings
also appear; this repair does not alter dependencies or certify their provenance.

The first proof now locally binds Hilbert Nontrivial directly to
`FilteredGNSHilbertNontrivial.globalGNSHilbertColimitNontrivial Stage sys ω`.
It then locally binds bounded-endomorphism Nontrivial using the native instance
in Mathlib `Topology/Algebra/Module/ContinuousLinearMap/Basic.lean:411`, whose
premise is exactly Nontrivial of the module. This cuts off rediscovery of global
GNS nontriviality during RingHom.injective elaboration. No new mathematical
assumptions, carriers, budgets, or linter settings; no hand-written replacement
for the native zero/id construction.

No compiler/build/test run. Parent AA/serial QA must confirm elaboration.
