# Stream 6: complement-preserving hyperbolic orbit

Source candidate ComplementHyperbolicOrbit20261024.lean. Arbitrary CommRing R,
Ring A, Algebra R A; existing DeBruijnRotorAlternationCycle.IsDualSeedPair d B.
Use native poles P=dB, M=Bd, support Delta=P+M, complement 1-Delta,
Q=d+B and J=d-B. No new pair predicate or carrier.

The existing Algebra.ChiralRealHyperbolicRotor uses an involution squaring to
full 1. Here Q squares to Delta and may vanish on the complementary support.
Define only the missing polynomial H(u,v)=(1-Delta)+u•Delta+v•Q and its pole
orbits. Derive the addition/product law, inverse H(u,-v) when u*u-v*v=1,
plus orbit u*u•P-v*v•M-u*v•J, minus orbit with exchanged poles/sign.
Derive idempotence and mutual orthogonality by actual inverse cancellation;
derive sum Delta, compression u*u•P, displacement square -(v*v)•Delta.
Polynomial expansions and compression need no normalization.

Reuse ReflexiveNilpotentFlows.support_table, complement_annihilates,
GrassmannianBundleCyclotomicOrientability.active_support_absorbs and existing
Stream5 finite pole/velocity facts. Separate elliptic consumer: the existing
normalBundlePart P (movingPolePlus c s d B) equals the existing
UnifiedGeometryOperatorSignificance.kmsModularWeight s c d B, with no circle
hypothesis. This is an algebraic diagonal projection, not a state/KMS assertion.
No metric, positivity, analytic flow, or noncompact-group classification claimed.
No builds/live edits. Candidate requires independent AA and serialized QA.
