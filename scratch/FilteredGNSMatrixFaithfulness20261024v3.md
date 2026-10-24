# Matrix GNS faithfulness v3 — explicit bounded-end witness

Uncompiled; no builds/tests or live edits. V1/v2 preserved.
All five theorem statements and imports unchanged. Original mathematical contract:
`FilteredGNSMatrixFaithfulness20261024.md`.

QA diagnostic: `/tmp/qa-a-matrix-faithfulness-v2-jj8eh4tb/compile.log`.
V2 still times out at the bounded-end Nontrivial `inferInstance` (line 45:40,
default 20000 typeclass heartbeats). Both letI bindings also trigger style warnings.

V3 uses `let` for both local instances. Hilbert nontriviality remains an explicit
application of the existing native instance. Bounded-end nontriviality is now
constructed with operators 1 and 0: an equality between them would, upon evaluation
at `globalGNSVacuum Stage sys ω i`, contradict native `globalGNSVacuum_ne_zero`.
No Nontrivial instance search occurs in this witness, no new hypotheses or carriers,
no increased budgets, and no linter suppression. The unrelated matrix-simplicity
`inferInstance` remains unchanged; it was not the failing search.

Parent AA/serial QA must confirm elaboration and warning status. Dependency dirty
warnings in the prior log are unaffected and are not certified by this candidate.
