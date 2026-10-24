# Filtered GNS vacuum readback: bounded candidate

Uncompiled, awaiting independent AA/QA. No builds, tests or live-owner edits.
Reuses globalGNSVacuum, gnsStageToHilbertColimit, filteredGNSMap_toPreGNS,
globalStageRepresentation_stage, representedCStarClosure, and the existing
native finite-GNS vacuum norm/expectation theorems.

Candidate proves vacuum norm one, transition independence and independence of
chosen stage; represented-stage expectation equals the compatible state's
functional. Defines one continuous linear vector functional on the existing
closure with norm bound obtained from Cauchy–Schwarz and the operator norm.
Normalization and positivity on star a * a are proved, not supplied as inputs.
The stage readback holds for any chosen vacuum stage and any observable stage.

Exact remaining technical boundary: FilteredGNSRepresentedCStarStateCompletion
assumes PartialOrder and StarOrderedRing on the closure before accepting a
State. The inspected closure owner constructs its CStarAlgebra, but no order
construction was established by this bounded scout. This candidate does NOT
add those instance assumptions or claim to construct State/PositiveLinearMap.
Packaging as native State requires an actual compatible order construction
and monotonicity proof. No new carrier or witness structure is introduced.

No claim of faithfulness, traciality, KMS evolution, or independent new kernel
receipt. Source feasibility only; elaboration remains for the parent's lane.
