# Motion consumer v6: explicit native closure CStar instance

NEW sandbox source only. v5 is preserved; no builds/live edits/budget changes.
Latest actual v5 log /tmp/qa-a-finite-first-v5-mys18q1w/compile.log now reaches
50:11 and fails synthesizing SeminormedRing of representedCStarClosure for
abstract omega, at500k. This supersedes the earlier import-layout failure; it
is not a mathematical counterexample or permission to increase limits.

Changes:
- Import accepted InfoGeometry.Canonical.FiniteExponentialMotion instead of
  scratch helper-v4. The accepted scratch alignment-v2 import remains.
- Before theorem statements, select named LOCAL CStarAlgebra instances for
  the matrix tower closure with abstract compatible state omega and for the
  actual finiteSeedCompatibleStageStates H hH beta. Both bodies are direct
  applications of native representedCStarClosureCStarAlgebra. These are not
  new hypotheses, a replacement norm, or a new carrier.
- All proofs and mathematical statements otherwise unchanged from v5, including
  whole-action/congr_fun and generator equality transport, finite-stage witness,
  actual seed injectivity, and the all-beta/nonzero-tilt motion conclusion.

The intended effect is to make superclass synthesis use the exact owner instance
without recursively searching through the closure definition/state construction.
No transparency attributes/unsafe options. Limits unchanged1M/500k. This proposal
is uncompiled; dependent conversion or later superclass search can still fail.
Serial QA must check before any acceptance claim.
