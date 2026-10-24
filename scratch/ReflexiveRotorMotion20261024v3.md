# Reflexive rotor motion v3: focused rewrite repair

Candidate: ReflexiveRotorMotion20261024v3.lean.
Same statements and primitive pair hypotheses as frozen v2.
Diagnostic: /tmp/qa-a-reflexive-rotor-v2-x99j8qlk/compile.log.

rotor_mul_plus now unfolds only rotor and performs the two outer add_mul
rewrites and scalar multiplication rewrites explicitly. It rewrites hjp before
any sub_eq_add_neg/distributivity can destroy the intact (d-B)*(d*B) factor.
The final additive normalization uses abel. The reported hjp/smul_neg non-use
was caused by that prematurely expanded factor; both now have explicit roles.
Removed the independently reported unused mul_neg in rotor_conjugate_plus.

rotor_conjugate_minus and rotor_minus_mul_plus now rewrite the two swapped
rotor occurrences with rotor_swap_parameters instantiated at the fixed d,B,c
and exact -s / -(-s) arguments. The unrestricted symmetric parameter-swap
lemma is no longer in either simp set, preventing the rewrite loop.

No altered conclusions, new assumptions/carriers, budget changes, builds,
tests, or live-owner edits. V2 remains frozen. Independent AA and serialized
QA are required. The analytic extension is a separate pending author task;
this repair neither imports it nor claims its derivative results.
