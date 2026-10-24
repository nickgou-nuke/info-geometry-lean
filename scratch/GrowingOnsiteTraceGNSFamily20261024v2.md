# Growing onsite trace-GNS family v2 repair

Same mathematical contract as GrowingOnsiteTraceGNSFamily20261024.md.
Source: GrowingOnsiteTraceGNSFamily20261024v2.lean, uncompiled.

Grounded repairs from /tmp/qa-a-onsite-trace-family-xo_ex7fg/compile.log:
- After reverse-equivalence injectivity, explicitly change to the native raw
  commutator identity, with the source matrix equivalence typed in full.
  This avoids simp producing residual symm.toRingEquiv coercions that do not
  match StarAlgEquiv inverse simp heads.
- Replace unrecognized S.map notation with the parenthesized, fully qualified
  existing filteredGNSIsometricDirectSystem expression followed by .map.

No carrier, family, bound, compatibility, or state semantics changed. All
CompatibleOperatorFamily fields remain proved from the actual onsite recursion,
trace state, all-index transport, and absolute summability. The completed
operator is still the native construction on the existing Hilbert colimit.
No budget changes/builds/live-owner edits. Original frozen candidate preserved.
AA and serialized QA required; downstream elaboration-sorry warnings in the
failed run are not treated as axiom-audit evidence.
