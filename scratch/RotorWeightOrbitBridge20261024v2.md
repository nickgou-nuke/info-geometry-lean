# RotorWeightOrbitBridge v2: native name resolution

Source: RotorWeightOrbitBridge20261024v2.lean; frozen v1 preserved.
Same seven declarations and B/C/D/E contract as RotorWeightOrbitBridge20261024.md.
Diagnostic: /tmp/qa-a-rotor-weight-orbit-pi0lilkt/compile.log.

Every code occurrence of rotor is now explicitly ReflexiveNilpotentFlows.rotor,
which has arbitrary CommRing scalar R through Algebra R A. This prevents the
imported real-scalar rotor from capturing the generic-R statements/unit values.

All broad opens are narrowed to explicit lists: native inverse/conjugation/support
lemmas; PeirceWeightedTrace.supportWeight; TracialCARDensity weighted,
weighted_apply and joint_covariance; NCG.TracialFunctional. Stream5's pair,
phaseRotor and movingPolePlus and Stream1 unitOrbitMap already use narrow opens.
Other native names (Stream3 weight, real-time path/derivative, Grassmannian bracket)
are already namespace-qualified. No new aliases or definitions are introduced.

No changes to intended formulas, assumptions, units, readouts, or actual paths.
No builds/tests/live-owner edits/transparency changes/budget increases.
The v1 run stopped at maxErrors, so this repair does not claim that the later
proofs have passed; independent AA and serialized QA remain required.
