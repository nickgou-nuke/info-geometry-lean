# Native tracial GNS right multiplication

Source-only candidate: TracialGNSRightMultiplication20261024.lean.

Input: any NonUnitalCStarAlgebra A with its partial/star order, a native positive
complex linear map f, and primitive cyclicity f(a*b)=f(b*a) for all a,b.
No faithfulness, normalization, unitality, or normed structure on PreGNS is assumed.

Construction on the SAME native carriers:
- preGNS_norm_def plus cyclicity proves tracial_preGNS_star_norm.
- leftMulMapPreGNS_norm_le extracts the bound already used by Mathlib's
  leftMulMapPreGNS via LinearMap.mkContinuous_norm_le.
- tracial_preGNS_right_mul_norm_le applies that bound to star b and star a.
- rightMulLinearPreGNS is [x] -> [x*b] on the native PreGNS type synonym.
- rightMulMapPreGNS packages this linear map using its proved bound.
- rightMulMapGNS uses ContinuousLinearMap.completion on native f.GNS.
- Representative readback, the completed pointwise bound, and operator norm
  bound <= norm b are supplied. Completion uses closedness and native density;
  no injectivity/separation claim about PreGNS is made.

Search: Mathlib GelfandNaimarkSegal.lean owns left multiplication and completion;
repo-wide rightMul/GNS and tracial-star searches plus the relevant FilteredGNS,
GNSMathlibBridge, CompletedGNSCovariance, Cl11TraceGNSHilbertColimitBridge owners
found concrete M2 right-action comparisons but no general native right CLM in
those sources. This is a bounded reuse claim, not a global absence assertion.

The growing commutator tower, right-action adjoint law, and compatibility of
successive Hamiltonians are later consumers; this file does not assert them.
No new Hilbert carrier, replacement GNS, conclusion bundle, or custom axiom.
No builds/tests/live-owner edits. Requires independent AA and serialized QA.
