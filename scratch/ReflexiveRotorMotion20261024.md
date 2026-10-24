# Native reflexive rotor motion candidate

Source: `ReflexiveRotorMotion20261024.lean` (scratch only, uncompiled).
Grounding: frozen `ReflexiveRotorMotionContract20261024.md`.
Import: `InfoGeometry.Canonical.ReflexiveNilpotentFlows` only.
Namespace extends the existing native ReflexiveNilpotentFlows namespace.
No new definitions, structures, aliases, carrier, or bundled conclusion packet.

## Hypotheses and scope

Ring A, square-zero d and B, and the two primitive reflexive laws dBd=d,
BdB=B. Scalar theorems add CommRing R and Algebra R A, supplying central
scalar action. No star, characteristic-zero, positivity, or topology premise.
The generic commutator [d-B,d+B]=2(dB-Bd) needs no pair relations.

## New focused declarations

- skew_commutator_plus/minus/parity/sum and
  skew_double_commutator_parity use the existing Grassmannian lieBracket.
  Signs: [J,P+]=-Q, [J,P-]=Q, [J,Gamma]=-2Q, [J,Q]=2Gamma,
  and [J,[J,Gamma]]=-4Gamma.
- skew_commutator_plus_eq_zero_iff detects precisely d=B=0 without dividing
  by 2 or 4. It does not use the double commutator as a no-turn test.
- rotor_mul_plus, plus_mul_rotor, creator_mul_rotor are small multiplication
  lemmas for the actual rotor, using the native support table/absorption.
- rotor_conjugate_plus/minus are generalized polynomial formulas for every
  c,s, with negative/positive mixed terms respectively; normalization unused.
- rotor_swap_parameters is the generator-exchange identity.
- rotor_reverse_inverse specializes native rotor_inverse at c,-s.
- rotor_plus_idempotent/minus_idempotent reuse native
  isIdempotentElem_homogeneousProj; rotor_plus_mul_minus/minus_mul_plus prove
  both zero products using the native inverse and support table.
- rotor_projector_sum and rotor_projector_resolution prove the active support
  sum and total sum one with the existing complement. These and the preceding
  inverse-based laws require exactly c*c+s*s=1.
- rotor_quarter_turn_plus/minus specialize the universally proved formulas.
- rotor_quarter_turn_fixed_iff and rotor_no_turn_iff prove the zero-pair
  equivalences; no-turn quantifies ALL normalized scalar pairs, and the forward
  implication uses (0,1). No fixed-parameter h_exp hypothesis is reused.

These are idempotents in an associative ring, not star projections. An algebraic
commutator oscillator is not an analytic ODE theorem. There is no exponential,
continuity, differentiation, de Bruijn, or classification claim.

All prior FreshTail files are preserved. No live-owner edits, builds, tests,
custom axioms, placeholder proofs, or budget changes. Independent AA and
serialized kernel QA are required before promotion. Suggested audit heads:
rotor_conjugate_plus, rotor_conjugate_minus, rotor_plus_idempotent,
rotor_minus_idempotent, rotor_plus_mul_minus, rotor_minus_mul_plus,
rotor_projector_sum, rotor_projector_resolution, skew_double_commutator_parity,
skew_commutator_plus_eq_zero_iff, rotor_quarter_turn_fixed_iff, rotor_no_turn_iff.
