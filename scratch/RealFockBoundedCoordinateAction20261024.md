# Actual bounded coordinate action on algebraic FockInfinity

NEW source only: RealFockBoundedCoordinateAction20261024.lean.
Imports intended InfoGeometry.Clifford.RealFockCoordinateTransport (pending
AA/QA/promotion), accepted RealFockHilbertCompletion, and the native
ClNNFockDirectLimitRepresentationLinearityWave16 owner. No builds/live edits.

Bundle the EXISTING function splitCliffordFockAction a as a real LinearMap
using its existing add_right/smul_right theorems. Do not construct another
DirectLimit lift or action. Expose definitional application readback.

Prove arbitrary mixed-stage readback at max(m,n): move the Clifford element
with splitCliffordMap and spinor with fockStageMap, using native Algebra.of_f,
Module.of_f and splitCliffordFockAction_of. No compatibility assumption.

For each actual colimit image of fockCreationGenerator m i or
fockContractionGenerator m i, represent an arbitrary algebraic spinor at stage n.
Apply mixed-stage readback, accepted stage norm preservation and the pending
transported_creation_norm_le / transported_contraction_norm_le, whose inputs
are arbitrary later-stage spinors. Deduce norm(action psi)<=norm psi globally.

Use that proved bound in LinearMap.mkContinuous 1 for two concrete CLMs; prove
application is definitionally the original splitCliffordFockAction on the
actual coordinate colimit element, and derive operator norm<=1. Preserve exact
native metric instance names locally. No assumed bounds/compatibility, no
new carrier, replacement action, or completion operator. This is an algebraic
carrier CLM prerequisite; completion is intentionally left to a later owner.
All statements remain source-only until dependency and candidate pass QA.
