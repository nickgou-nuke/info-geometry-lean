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

## V3: accepted native API alignment (no compilation)
Native FiniteSeedRepresentedRealTime is now present; API re-read for this revision.
The v2 compile log is /tmp/qa-a-tilt-motion-v2-0hcfp187/compile.log. It terminated
at maxErrors=3, so later proof bodies are not claimed validated.

- Match the native shared universe: I:Type u, Stage:I→Type u, matrix index n:Type u.
  Previously the independent Type* binders left the native closure application
  misaligned. Explicitly parenthesize its carrier `(representedCStarClosure
  Stage sys ω : Type u)` in both f's target and a's binder.
- Open the actual declaration namespace AlgebraicKMSStateColimit for
  finiteSeedCompatibleStageStates (defined in FiniteSeedGibbsCStarStates.lean:136).
- Replace deprecated push_neg with push Not.
- No mathematical weakening, new instances, increased budgets, linter suppression,
  new carriers or alternate flow. The native simplicity instance remains reused.

V1/v2 and the independent Fock candidate are preserved. No live edits, builds or
tests. Parent serial QA must check the remaining proof bodies after these front-end
fixes. Earlier sections describe the historical v1/v2 dependency status; this
revision uses the now accepted native real-time owner.

## V4 structural elaboration repair
Source diagnostic: /tmp/qa-a-tilt-motion-v3-n1gs4f50/compile.log (three errors,
remaining bodies not fully checked). No budgets are raised in this candidate.

1. New expUnitary_conjugation_eq_complexPath normalizes exp/star/scalars over an
   abstract CStarAlgebra A, matching the accepted real-time owner's helper pattern.
   The represented action identification now only applies that generic theorem to
   the existing matrixGenerator, avoiding dependent closure reduction inside simp.
2. New representedMatrixStageMap_equiv_injective does the Subtype.val and stage
   readback argument with arbitrary Stage/sys/ω. The concrete seed injectivity
   theorem applies it; native imported matrix simplicity remains reused.
3. Explicit private abbrev matrix CStar/order/star-order families are installed
   locally, matching the accepted native real-time owner. Local closure CStar and
   Ring abbreviations use the canonical native instance and its literal projection,
   to shorten HMul synthesis without introducing a different algebra structure.

All original mathematical conclusions are preserved, including every β and some
real time moving the actual seedRealTimeAut observable. No assumed faithfulness,
new flow, carrier, conclusion bundle, budget increase or linter suppression.
V1–v3 and the independent Fock candidate are preserved; no compilation or live edit.
Serial QA must confirm whether these structural changes resolve elaboration.
