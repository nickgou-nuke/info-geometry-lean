# Action alignment v2: transport the proved whole-automorphism equality

New sandbox only, no builds/live edits. Preserve v1 and accepted injectivity.
Exact terminal log: /tmp/qa-a-seed-action-alignment-epxneze_/compile.log.
Only line47:2 failed: the pointwise theorem's rfl proof timed out at isDefEq 1M.
The prior whole-automorphism theorem (line34, rfl line38) had no error.
The pointwise statement elaborated before its proof failed. This is evidence
against declaring a demonstrated incompatible instance or header failure.

Native seedRealTimeAut is a def returning matrixRealTimeAut on the ACTUAL
Gibbs family and ACTUAL seedStageHom. matrixRealTimeAut returns a StarAlgEquiv
whose application is provided by its inherited function-like machinery. The
whole automorphism equation already avoids rebuilding a concrete Hilbert CLM.

Minimal v2 change: retain that whole-automorphism equality and apply
Mathlib DFunLike.congr_fun (Data/FunLike/Basic.lean:201) to the same actual
seedStageHom H hH beta x. It transports equality to application without asking
rfl to compare the two large applied definitions afresh. No new hypothesis,
replacement action, carrier, state, typeclass instance, or transparency setting.
The actual pointwise statement is unchanged. Namespaces differ only to preserve
v1 as an independent frozen diagnostic module.

The failure mechanism is NOT proven to be a definitional instance mismatch.
If congr_fun fails, capture the first diagnostic; it may still need expensive
function-like/result-type alignment. Do not claim this proof-term change solves
that cost before serial QA. If it passes, downstream motion should rewrite this
application API rather than rely on a single defeq-heavy exact specialization.
No new full motion candidate is included in this diagnostic.

Native byte identities checked:
FiniteSeedRepresentedRealTime: de19e22b0619c2d9a743dac42355971c4223c27bffeb41033b7ff1135862232e
FiniteSeedRepresentationFaithfulness: eff6a9847572d55866cfba5fae4474a4c651b84df6f9137fdf05c1527437e2b0
Budgets remain the existing 1M/500k baseline; no increase or unsafe options.
