# Density exponential v4: independent generic helper and exact native consumer

NEW sandbox files only:
- FiniteMappedGibbsDensityExponential20261024.lean
- FiniteSeedRepresentedDensityExponential20261024v4.lean

V1–v3 and all native owners remain untouched. No builds/tests run by author.
No budget, transparency, unsafe, carrier, state or hypothesis changes.

## Diagnostic and scope

/tmp/qa-a-density-exponential-v3-u3niehtd/compile.log records first errors
at the concrete theorem statement line117: SeminormedRing, Ring and
TopologicalSpace synthesis on the actual represented closure timed out at
20,000 typeclass heartbeats. No generic-proof errors precede them in this log.
That is NOT standalone generic axiom/strict acceptance, nor concrete acceptance.

The new helper is the v3 prefix through the four generic mathematical lemmas,
with proof bodies and native CFC instance choices unchanged. It retains the
same imports to avoid an unrelated import minimization change. Its statements
are map_gibbsDensity_eq_cfc, cfc_expWeight_eq_exp, map_gibbsDensity_eq_exp,
and map_gibbsDensityUnit_inv_eq_exp. Standalone QA can now check this module
without attempting the concrete declarations. Namespace remains identical;
never import old v3 and this helper together as two owners of these heads.

The v4 consumer imports that helper rather than copying it. Before the two
concrete declarations, a named LOCAL seedClosureCStarAlgebra explicitly calls
FilteredGNSRepresentedCStarClosure.representedCStarClosureCStarAlgebra
on CStarMatrixStage, cstarMatrixInductiveSystem, and the exact
finiteSeedCompatibleStageStates H hH beta. This is the native closed
StarSubalgebra C⋆ structure, not a postulated instance or new norm.
Stage family instances, concrete statements and their proof bodies stay as v3.

The exact outputs remain, for every Hermitian H and real beta:
- representedDensityUnit value = exp((-beta) • seedStageHom H hH beta H);
- inverse of that same actual unit = exp(beta • seedStageHom H hH beta H).
No supplied equality, injectivity, beta positivity, state faithfulness,
normalization, analytic KMS or complex-time extension premise.

Native grounding: Canonical/FilteredGNSRepresentedCStarClosure.lean:46,55
(the actual closed star subalgebra and inherited CStarAlgebra instance),
FiniteSeedRepresentedRealTime seedStageHom and representedDensityUnit,
and the v3 contract's CFC map/scaling/native exponential inverse derivation.

This repair is an elaboration proposal, not a proof of its own typeclass success.
QA must verify the local instance is used without changing the underlying
structure and that both concrete declarations elaborate at unchanged defaults.
Independent AA and serialized helper-then-consumer QA remain required.
