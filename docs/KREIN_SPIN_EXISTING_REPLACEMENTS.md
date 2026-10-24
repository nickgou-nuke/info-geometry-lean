# Existing Krein and fixed-Cartan replacements

This record classifies three source-reviewed families. It reuses existing
constructive proofs instead of duplicating carriers or removing counterexamples.

## Indefinite Hodge kernels

`HodgeCohomology.KreinHodgeDiracTests` constructs a self-adjoint square-zero
operator for a nondegenerate indefinite pairing. Its square kernel is larger
than its kernel. The production owner `KreinHodgeDirac` proves the signed
energy identity and obtains kernel equality under image anisotropy, or under
positivity of the symmetry-weighted pairing together with commutation with
the symmetry. Self-adjointness alone is insufficient.

For the separate bounded null model on the existing `DoubledSpace ℝ`,
`KreinNullContraction` constructs an explicit continuous homotopy h with
h²=0 and dh+hd=1. Every d-closed vector has a unique primitive in ker h.
The homotopy is not the indefinite adjoint. This gives constructive exactness,
not an identification of indefinite harmonic vectors with homology.

## Ordinary trace and supertrace

`Modular.KreinPotentialTrace` retains the identity-matrix counterexample.
Its full-carrier conversion law is tr A = str A + 2 tr A₂₂. For a Krein
square of the block matrix [[A,B],[C,D]], the correction is
2(tr(DᴴD)-tr(BᴴB)). Over ℂ, equality of the two traces is equivalent to
equality of those Gram traces. A consumer must prove that balance or retain
the correction; no unconditional identification survives.

## Fixed-Cartan spin mixing

`Physics.SpinAffineCasimirRigidity.hyperbolic_counterexample` preserves the
ladder-ladder bracket but violates the fixed-Cartan ladder relation.
`fixed_cartan_spin_relations_iff` exactly characterizes the two specified
relations within the stated complex coefficient ansatz: v=0 and normSq u=1.
`Physics.SpinPhaseRealization` realizes these coefficients by the actual
unitary matrix diag(u,1), proving both ladder and Cartan conjugation formulas.
This is a constructive realization of the allowed family, not a restriction
asserted without examples. No classification outside this ansatz is claimed.

## Verification

`Canonical.KreinSpinPositiveAudit` imports existing kernel/trace audits and
adds the contraction, counterexample, rigidity, and phase-realization heads.
Parent locked compilation passed (session 97539, terminal exit 0, 8952 jobs),
with evidence in `/tmp/krein-spin-positive-audit.log`. Independent semantic
review passed with the carrier distinction above. Scoped staged diffs are
clean. A further parent replay passed in session 1283 (terminal exit 0,
8979 combined jobs), log `/tmp/shear-euler-krein-build.log`. The earlier
compiler-lane wait has ended. Independent QA accepted the combined batch in
session 69457 (terminal exit 0, 8980 jobs), log
`/tmp/shear-euler-krein-final-qa.log`. The imported Hodge audit prints thirteen
reports, the imported trace audit four, and this audit nine additional heads;
all use exactly `propext`, `Classical.choice`, `Quot.sound`. There are no
scoped-source warnings; strict screening, scoped diffs, and hole checks pass.
This record does not certify unrelated sources or exhaustive discovery.
