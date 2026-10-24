# Actual bounded coordinate action on algebraic FockInfinity

NEW source only: RealFockBoundedCoordinateAction20261024v2.lean.
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

## v2 exact topology alignment

Receipt: /tmp/qa-a-fock-bounded-action-b0mc15wz/compile.log. All preceding
mixed-stage readbacks and global bounds passed; the CLM signature selected
instTopologicalSpaceQuotient while mkContinuous returned the metric topology.

Add proper named local instances fockInfinityMetricUniformSpace and
fockInfinityMetricTopology, both literal projections of the accepted native
fockInfinityNormedAddCommGroup.toMetricSpace. This selects already constructed
data, not a new topology/norm definition or an assumed equivalence of topologies.
Do not assert that the generic quotient topology equals the metric topology.
Use splitCliffordFockActionLinearMap_apply explicitly in each mkContinuous
bound proof instead of relying on semireducible unfolding.

Native completion owner audited: RealFockHilbertCompletion constructs its norm
from the definite pairing, then InnerProductSpace/NormedSpace and scalar uniform
continuity; RealFockCompletion abbreviates UniformSpace.Completion FockInfinity
under those native metric instances. Its stage injection is the composition of
the metric stage isometry and Mathlib toComplₗᵢ. No owner/carrier redefinition is
needed here. This candidate reuses that exact norm's uniform-space projection.
Downstream completed-action v1 should remain frozen. A later revision must
reactivate these exact two named local instances along with the existing metric
instances before completion/CLM expressions; its current source should not be
claimed aligned until checked by QA. No new completion carrier is authorized.

Frozen v1 unchanged. No builds, live edits, budget or transparency changes.
v2 is uncompiled and requires independent AA/QA.
