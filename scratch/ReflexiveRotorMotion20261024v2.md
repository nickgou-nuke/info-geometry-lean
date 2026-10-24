# Reflexive rotor motion v2: hypothesis scope repair

Candidate: ReflexiveRotorMotion20261024v2.lean.
Same mathematical contract as ReflexiveRotorMotion20261024.md.
Source-only repair from /tmp/qa-a-reflexive-rotor-motion-n2umglxy/compile.log.

Adds `include hd hB hr hs` immediately after the Scalars pair variables.
These explicit primitive pair premises are now included in all dependent
scalar theorem declarations, matching their existing call sites and intended
contract. `omit hd hB hr hs in` precedes the rotor_swap_parameters docstring:
that identity remains hypothesis-free. Earlier ring commutator lemmas already
bind their needed hypotheses explicitly; skew_commutator_sum remains free of
pair premises. All other scalar proofs consume pair premises directly or via
native/preceding lemmas.

Removes only the reported unused sub_zero simp argument in skew_commutator_plus.
No proof conclusions, definitions, carriers, normalization conditions, or
budgets changed. V1 remains frozen. No builds/tests or live-owner edits.
The QA log stopped at maxErrors before later scalar proofs, so further kernel
checking remains necessary; this is not a claim that those proofs passed.
