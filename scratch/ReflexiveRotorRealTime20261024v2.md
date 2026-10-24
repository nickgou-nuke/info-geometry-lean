# Reflexive rotor real-time v2: extensional path normalization

Candidate: ReflexiveRotorRealTime20261024v2.lean, uncompiled scratch only.
Same contract, paths, hypotheses, and conclusions as frozen v1.
Diagnostic: /tmp/qa-a-rotor-real-time-lomdo30w/compile.log, lines46 and153.

Both diagnostics display pointwise function sums/differences on the derived
side and explicit path expressions on the target side, in addition to printed
additive-group instance projections. This revision first addresses function
normalization explicitly; it does not assume those projections prove a genuine
incompatible-instance diamond.

- hasDerivAt_realRotor_coefficients proves the nested pointwise function sum
  equals realRotor by funext and Pi.add_apply, unfolding only realRotor/rotor.
  Rewrites this exact function equality in the derivative proof, then removes
  zero_add from the derivative coefficient.
- hasDerivAt_deriv_rotorOrbit names the derived difference hdiff, proves its
  pointwise function difference equals the explicit Lie-bracket lambda by
  funext and Pi.sub_apply/lieBracket, then rewrites that equality in hdiff.
  The derivative coefficient is definitionally the existing double bracket.

No new instances, conversions between different carriers, transparency options,
or budget changes. Actual continuity, initial -Q, and actual second derivative
claims Gamma''=-4Gamma and P''=2Delta-4P remain intact. V1 is untouched.
No builds/tests/live-owner edits. Independent AA and serialized QA required;
if a genuine instance mismatch survives function normalization it will need
its own source-grounded repair, not an unsupported verification claim here.
