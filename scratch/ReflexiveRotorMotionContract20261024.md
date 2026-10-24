# Reflexive rotor motion: bounded source contract

Read-only owner audit; no Lean implementation or kernel receipt in this task.

## Exact native reuse

Canonical/ReflexiveNilpotentFlows.lean, namespace
InfoGeometry.Canonical.ReflexiveNilpotentFlows:
- support = d*B+B*d, complement = 1-support, weyl/complement+(d-B).
- support_sq, complement_annihilates, support_table: active/complement routing.
- weyl_swap_supports: quarter-turn exchanges d*B and B*d.
- rotor c s d B = complement d B + c • support d B + s • (d-B) (line133).
- rotor_mul (line226): independently quantified c,s,e,t, circle product law.
- rotor_inverse (line248): c*c+s*s=1 gives rotor c s * rotor c (-s)=1.
  Reverse inverse follows by applying the same theorem at c,-s.
All use raw hd:d*d=0, hB:B*B=0, hr:d*B*d=d, hs:B*d*B=B;
no extra pair structure is needed.

Algebra/UnipotentReflexivePairFactorization.lean: skew_square,
support_mul_skew, skew_mul_support already give J²=-Delta and support absorption.
Canonical/GrassmannianBundleCyclotomicOrientability.lean:
active_support_absorbs (646), active_support_idempotent (657).
Canonical/RootsOfZeroUnityMoebiusModularG22.lean already names polePlus,
poleMinus, chiralParityRoot, diracRootPlus, hodgeStarRootMinus; its
 diracRootPlus_sq proves Q²=Delta. Do not introduce duplicate primitives.
Canonical/UnifiedGeometryOperatorSignificance.lean also has projPlus/projMinus,
ehresmannCurvature=Gamma and kahlerStructure=J; importing that broad synthesis
owner is unnecessary for a narrow polynomial bridge.

## Minimal proposed extension, not found in the inspected reflexive flow owners

Use the existing rotor in its native namespace or a small consumer module.
Below P+=dB, P-=Bd, Delta=support, P0=complement, J=d-B, Q=d+B,
Gamma=P+-P- are notation for existing expressions, not new definitions.
Bracket means XY-YX.

Ring-only identities under the four raw pair laws:
[J,P+]=-Q; [J,P-]=Q; [J,Gamma]=-2Q; [J,Q]=2Gamma;
[J,[J,Gamma]]=-4Gamma. Natural integer multiples are repeated addition;
no characteristic-zero premise or division is required. This last identity
is an algebraic oscillator relation, not a differential equation theorem.

Over CommRing R, Ring A, Algebra R A (central scalar action), for ALL c,s:R:
rotor c s d B * P+ * rotor c (-s) d B
  = (c*c) • P+ + (s*s) • P- - (c*s) • Q.
The P- expression interchanges P+/P- and has PLUS (c*s) • Q.
No circle normalization is needed for these polynomial equalities.
Proof: expand existing rotor, use complement_annihilates/support_table and
raw four pair relations. Do not recreate rotor multiplication/inverse proofs.

Under c*c+s*s=1, conjugation preserves the two idempotents and their
orthogonality; their sum is Delta and adjoining P0 yields 1. Reuse both inverse
orders and support_table, rather than assuming moving projector laws.
Without normalization their sum is (c*c+s*s) • Delta, not generally Delta;
without star hypotheses these are idempotents, not orthogonal projections.

## Precise no-turn scope

Ring-only infinitesimal contract: [J,P+]=0 iff d=0 and B=0.
Use [J,P+]=-Q; Q=0 gives B=-d, hence reflexivity and d²=0 force d=0,B=0.
No cancellation of 2 or 4, so this works in characteristic two as well.

Finite contract: (for every normalized c,s, rotor c s * P+ * rotor c (-s)=P+)
iff d=0 and B=0. The reverse implication is direct; forward specialize at
(c,s)=(0,1), using native weyl_swap_supports or the general polynomial formula.
Then P+=P-, their zero cross-product and idempotence imply P+=P-=0;
reflexivity forces both generators zero. A single fixed angle is NOT enough:
(1,0) fixes every pair. Even the quarter-turn equality suffices.
Vanishing double commutator alone is NOT the no-turn criterion in arbitrary
characteristic; do not cancel 4 or infer Gamma=0 from it without extra hypotheses.

## Quantification and analytical boundary

A hypothesis h_exp for fixed c,s cannot be reused at (0,1) or (1,0).
First prove the polynomial formula universally in c,s; specialize that theorem.
Alternatively an external formula premise must itself quantify all parameters.
No h_exp premise is needed for the native rotor polynomial.

Actual real-time sin/cos specialization, exponential identification, continuity,
and derivatives require separate scalar/topological analytic hypotheses and
proofs. Ring identities establish none of these by themselves. No de Bruijn
syntax, normalization, or theorem-prover universality claim follows.

This bounded audit searched reflexive, rotor, Peirce and related support owners;
it is not a repository-wide absence certification. No duplicate carrier or
primitive is proposed. FreshTail candidates are untouched by this contract.
