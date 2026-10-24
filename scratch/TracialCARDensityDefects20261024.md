# Tracial CAR density defects: narrow extension contract

G-A authorship, 2026-10-24. UNCOMPILED. No builds/tests; independent Popper AA
and Ampere QA remain pending. Existing owners and other agents' work untouched.

Only import: InfoGeometry.OperatorAlgebra.TracialCARDensity.
Namespace: InfoGeometry.OperatorAlgebra.TracialCARDensity (same as live owner).
No new definitions, carriers, predicates, bundles, or forwarding wrappers.

Actual source dependencies:
- NCG/NoncommutativeCyclicCocycle.lean: InfoGeometry.NCG.TracialFunctional,
  its cyclic and map_sub laws.
- OperatorAlgebra/TracialCARDensity.lean: weighted, density,
  density_mul_ann, ann_mul_density, density_mul_cre, cre_mul_density.
- OperatorAlgebra/CARProjectors.lean: plus=ann*cre, minus=cre*ann,
  chirality=plus-minus, projectors_add.
- Physics/SplitCliffordAlgebras.lean: SplitClifford.CARPair, through imports.

Ambient hypotheses are CommRing R, Ring A, Algebra R A. A CARPair supplies
primitive nilpotence and normalized anticommutation; no desired density
conclusions are assumed. The general weighted defect needs no CAR pair.

Six separate new statements:
1. weighted_commutator_defect:
   weighted tau rho (x*y-y*x) = tau ((rho*x-x*rho)*y).
2. density_commutator_majorana_plus:
   [rho,ann+cre] = (c-a) • (ann-cre).
3. density_commutator_majorana_minus:
   [rho,ann-cre] = (c-a) • (ann+cre).
4. density_anticommutator_majorana_plus:
   {rho,ann+cre} = (a+c) • (ann+cre).
5. density_anticommutator_majorana_minus:
   {rho,ann-cre} = (a+c) • (ann-cre).
6. two_smul_density:
   (2:R) • rho = (a+c) • 1 + (c-a) • chirality P.

Here rho=density P a c=a • (cre*ann)+c • (ann*cre): occupation weight a,
vacuum weight c. Brackets in this document are abbreviations for explicit
ordered products in the Lean statements, not new definitions. The first proof
uses cyclicity; the four Majorana identities reuse the existing eigenproducts;
the last uses the existing complementary-projector sum. No generic square,
CAR transport, or finite pairing theorem is duplicated.

All are division-free polynomial identities. No inverse of two, positivity,
star compatibility, normalized state, tracial iff converse, nonzero defect,
analytic KMS, GNS completion, or new vacuum transport assertion is claimed.
Proof elaboration, warnings and transitive axioms await QA. No linter settings
are added or disabled in this candidate.
