# Actual seed motion v11 — contract before implementation

New sandbox only, uncompiled, no builds/live edits. Prior versions preserved.
Dependency: newly native Canonical.FiniteSeedRepresentationFaithfulness,
seedStageHom_injective in that module's namespace. Parent reports direct scratch
QA passed; native dependency QA remains queued, not inferred complete here.

Preserve the final target for EVERY real beta and EVERY nonzero real h:
let J := seedStageHom (k:=1) (h•tilt2) (tiltHamiltonian_isHermitian h) beta;
exists real t, seedRealTimeAut (h•tilt2) ... beta t (J switch2) ≠ J switch2.
Same native Gibbs family, represented closure and positive-time unitary flow.

Reuse earlier v10 generic exponential-path proof and normalization identity.
Derive generic matrixRealTimeAut existence of motion from an injective actual
matrix hom and a nonzero raw commutator, resolving map_zero/map_mul in the generic
context. Specialize with the actual seedStageHom and the new native injectivity
proof, NOT the old expanded representedMatrixStageMap_equiv_injective route.
Then reuse the finite tilt/switch entry01 witness (2*h≠0).

No local/global reducibility attributes, no alternate state, no assumptions of
faithfulness/motion on the concrete seed. Same 1M/500k baseline; no increases.
The concrete action wrapper may still require normalization; success is not
claimed until serial QA. Isolate a generic-seed existence lemma before the final
tilt specialization to locate any remaining failure. Do not re-prove matrix
faithfulness, introduce duplicate simplicity instances, or copy coe-readback APIs.
No new derivative calculation: use native
ModularFlowExponentialGenerator.hasDerivAt_complexExponentialConjugationPath_zero.
The theorem asserts some moving time, not every nonzero time, and does not
contradict invariance of the represented Gibbs state.
