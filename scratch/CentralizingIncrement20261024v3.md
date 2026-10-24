# Centralizing-increment criterion and native boundary obstruction

Uncompiled sandbox candidate; no builds or live edits. Generic carrier: existing
RingHom e:A→+*B, Rings A/B, no new structure or assumptions on characteristic.
Prove pointwise and universal equivalences:
[K,e(a)] = e([H,a]) iff Commute (K-e(H)) (e(a)).
Proof is distributivity and additive cancellation, with no division or 2-cancellation.

Concrete source: Canonical/CuntzMatrixTraceTower.concreteStep 1 sends A to the
reindex by stageIndexEquiv 1 of A⊗I₂. Physics/KleinBottleSewingExact supplies
actual tilt2=diag(1,-1) and switch2. Define only the actual boundary matrix
boundaryZZ := reindex(stageIndexEquiv 1)(tilt2⊗tilt2), in native MatrixStage 2.
For λ:ℂ nonzero, prove λ•boundaryZZ does not commute with concreteStep 1 switch2,
then deduce H↦concreteStep 1 H+λ•boundaryZZ fails commutator compatibility on all
old matrices, for ANY old H. Real nonzero coefficients embed into this statement.

Reuse Mathlib Matrix.mul_kronecker_mul and reindexAlgEquiv, then the tensor
coordinate ((0,0),(1,0)) to expose λ=-λ over ℂ. No replacement 4×4 carrier.
The concrete obstruction is characteristic zero; generic criterion is arbitrary Ring.

Scope: strict commutator transport through the unital algebra embedding A⊗I,
and hence faithful trace-GNS representative transport. This is NOT a universal
obstruction to coupled growing models: a spin/Fock Hilbert embedding x↦x⊗vac
can be annihilated by newNumber on the vacuum, allowing oldZ⊗newNumber interactions.
No growing family, uniform bound, completion, or spectral claim is established here.
Parent AA and serial QA required. Nearby commutator owners were searched; no
centralizing-increment iff was found in the inspected native owners.

## V2 parser-only correction
QA log: /tmp/qa-a-centralizing-increment-h6ic614m/compile.log.
Replace the reserved Lean token λ by identifier lam throughout the Lean candidate
(including hλ→hlam). No mathematical statement/proof changes. V1 preserved.
No builds or tests; kernel checking remains for the parent serial QA lane.

## V3 definition/coercion alignment
QA source: /tmp/qa-a-centralizingincrement20261024v2-n5a5fm2p/compile.log.
The boundary matrix equality now explicitly unfolds local e, boundaryZZ and
concreteStep in simp only, alongside map_smul. The compatibility obstruction
explicitly changes the RingHom projections back to concreteStep applications
before additive cancellation. No mathematical or budget changes; no builds/live
edits. Previous candidates preserved; parent serial QA pending.
