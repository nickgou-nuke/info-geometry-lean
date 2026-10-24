# Actual represented tilt flow: nontrivial orbit

Uncompiled sandbox draft. No builds/live edits. Intended native import
`InfoGeometry.Canonical.FiniteSeedRepresentedRealTime` is pending integration;
API source inspected: scratch/FiniteSeedRepresentedRealTime20261024v3.lean.
The native FilteredGNSMatrixFaithfulness source exists; final native QA is pending.

## Contract
For h, β : ℝ with h ≠ 0, let H = h • tilt2 at stage 1 and let J be the EXISTING
seedStageHom H (tiltHamiltonian_isHermitian h) β. In the actual represented C⋆
closure for finiteSeedCompatibleStageStates H ... β, prove
J H * J switch2 - J switch2 * J H ≠ 0, and
∃ t : ℝ, seedRealTimeAut H ... β t (J switch2) ≠ J switch2.
No assumption on β; no claim every nonzero time moves the observable.
No new flow/state/carrier, no assumed injectivity, no analytic modular identification.

## Source-backed route
1. Canonical/FilteredGNSMatrixFaithfulness.globalStageRepresentation_injective
   proves stage injectivity from simplicity, using the native nonzero global vacuum.
   Reuse the imported native matrixStageSimple instance through typeclass synthesis;
   its private declaration name does not make its instance attribute local in this
   existing non-module owner. Do not redeclare simplicity. Coerce seedStageHom through
   Subtype.val and use algebraicColimitGNSRepresentation_of to read it back.
2. Physics/KleinBottleSewingExact defines tilt2 and switch2 and proves
   tilt2_switch2_anticomm, tilt2_sq, switch2_sq. The scaled commutator has 01 entry
   2*(h:ℂ); a short coordinate proof derives its nonzeroness. Map that genuine
   finite identity through J, using the proved injectivity.
3. Existing matrixRealTimeAut is Unitary.conjStarAlgAut of matrixUnitary;
   boundedGeneratorUnitary = selfAdjoint.expUnitary(t • G).
   Identify this same action with complexExponentialConjugationPath by unfolding
   the existing definitions, star_exp and selfadjointness; the sign is positive.
4. Canonical/ModularFlowExponentialGenerator.
   hasDerivAt_complexExponentialConjugationPath_zero gives derivative i•[G,X].
   HasDerivAt.unique against hasDerivAt_const refutes a constant orbit. This
   generic short lemma is applied to the actual represented seed action.

## Boundaries and validation
All statements are separate lemmas, not a conclusion packet. The coordinate
matrix witness alone is not the final consumer: final theorem mentions the
existing represented seedRealTimeAut explicitly. State invariance is compatible
with a nonconstant observable orbit, including at β=0.
No dependency/pin/cache changes. Parent promotes dependency first and performs
serial QA/axiom audit. Likely elaboration-sensitive points: CStarMatrix family
instance alignment and reduction of expUnitary/coercions, not mathematical gaps.

## V2 delta and source semantics
The sole Lean delta is deletion of the duplicate tiltFlowMatrixStageSimple instance.
All six theorem statements and proofs otherwise remain unchanged; v1 is preserved.
Native FilteredGNSMatrixFaithfulness.lean:84 declares `private noncomputable instance
matrixStageSimple` without `local` or `scoped`. Both owner and consumer use the
legacy import format (no `module` header). Lean Meta/Instances.lean registers the
instance with its AttributeKind in instanceExtension; private naming is not a local
instance attribute. Lean Environment.setExporting explicitly does nothing for a
non-module environment. The newer module-system public/private visibility filters
should not be confused with a `local instance` in this owner.

Expected synthesis at globalStageRepresentation_injective therefore reuses the
imported native instance. This is a source-level check, not a compile result.
No compilation until the real-time owner is accepted and parent assigns serial QA.
