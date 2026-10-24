# Actual completed creation/contraction operators

NEW source RealFockCompletedCoordinateAction20261024.lean only.
Intended native import InfoGeometry.Clifford.RealFockBoundedCoordinateAction is
pending AA/QA/promotion and transitively depends on RealFockCoordinateTransport.
Use accepted RealFockHilbertCompletion and its exact named local metric,
NormedSpace, and UniformContinuousConstSMul instances. No new carrier/action.

Mathlib Topology/Algebra/LinearMapCompletion.lean:45 defines
ContinuousLinearMap.completion on the actual UniformSpace.Completion carriers;
completion_apply_coe:60 states its value on every original vector. Use these
APIs directly to complete fockInfinityCreationCLM/fockInfinityContractionCLM.
RealFockCompletion remains the abbreviation of Completion FockInfinity.

Expose both algebraic coe readbacks and exact later-stage readbacks:
for h:m<=n, i:Fin m, psi:FockStage n, completed creation/contraction applied to
fockStageToCompletion n psi equals fockStageToCompletion n of the actual finite
CLM at fockModeShift m n h i. Derive via Algebra.of_f, native action_of and
transported coordinate readback. No assumed intertwining or compatibility.

Extend the actual algebraic <=norm estimate by Completion.induction_on:
closed inequality set via continuous CLM and norm; on coerced inputs use
completion_apply_coe, norm_coe and the already proved algebraic action bound.
Then ContinuousLinearMap.opNorm_le_bound with zero_le_one yields norm<=1.
This follows the native proof pattern in FilteredCompatibleOperatorNorm but
uses the real Fock carrier and actual constructed maps directly.

No completed CAR/adjoint laws are claimed in this module. They can be separate
density consumers after these exact operators/readbacks are accepted. No bound
or compatibility hypothesis fields, budgets, transparency changes, builds,
tests, or live edits. New candidate is source-only awaiting independent AA/QA.
