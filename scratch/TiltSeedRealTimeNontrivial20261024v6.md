# Represented tilt motion v6 — uncompiled candidate

Preserves the actual native seedRealTimeAut, every beta, nonzero real h,
and existence of some moving time. No all-nonzero-times claim.

Source diagnostic: /tmp/qa-a-tiltseedrealtimenontrivial20261024v5-u21kcv_x/compile.log.
No budgets raised: retained authorized 1M / 500k baseline.

The generic stage injectivity proof rewrites only representedMatrixStageMap and
StarAlgHom.comp_apply, applies Subtype.val, then uses the native
FilteredGNSRepresentedCStarClosure.algebraicColimitToRepresentedClosure_coe
and algebraicColimitGNSRepresentation_of. It no longer uses change to reduce the
dependent closure/representation. The signature eta-expands the hom application.
Existing globalStageRepresentation_injective and imported matrix simplicity
remain the faithfulness source; no faithfulness assumption or duplicate instance.

The concrete nonzero statement is now J(H*switch2-switch2*H) != 0.
This is equivalent to the prior product statement by hom laws, which are used
only in the new abstract CStar target helper. A generic existing-action lemma
transports that result through the native matrixRealTimeAut path identity.
Concrete specialization never writes multiplication of J H and J switch2.
No new flow, carrier, bundled conclusions, or weakened orbit conclusion.

Remaining QA question: whether eta-expansion and named coercion rewrites eliminate
all dependent elaboration costs. This is a proposed repair, not a compile result.
Earlier versions and Fock research preserved. No builds/tests/live edits.
