# Tracial CAR density candidate contract

Frozen G-A proposal, 2026-10-24. UNCOMPILED: no builds or tests performed.
Independent AA and kernel/axiom QA are required before promotion.

Exact imports:
- InfoGeometry.NCG.NoncommutativeCyclicCocycle
- InfoGeometry.OperatorAlgebra.CARProjectors

Exact reused types: InfoGeometry.NCG.TracialFunctional R A (not a namespace
named after its module) and SplitClifford.CARPair A. The latter is owned by
Physics/SplitCliffordAlgebras. CARProjectors supplies plus=ann*cre,
minus=cre*ann, idempotency, orthogonality and projectors_add. It supplies no
absorption theorem; this candidate derives ann_cre_ann directly from the
native anti and ann_sq fields, and cre_ann_cre via native particleHole.
The Clifford-specific CARFermionParity absorption lemmas are not general
CARPair theorems and are not imported as surrogate proofs.

Ambient assumptions: CommRing R, Ring A, Algebra R A. No new tracial or CAR
carrier, positivity hypothesis, nontriviality, division by two or field
assumption. Units are native Aˣ. weighted is a native linear-map composition.

Separate contracts:
- inverse_pullback and joint_covariance transport density and observables
  through unit conjugation; fixed-density invariance is not assumed.
- density P a c = a • minus P + c • plus P: a is occupation, c is vacuum.
- Four left/right eigenproducts have the corrected weights:
  rho*b=c b, b*rho=a b, rho*B=a B, B*rho=c B.
- density_mul_density derives the sector multiplication law using existing
  idempotency and orthogonality; both adjugate products equal (a*c) • 1.
- divisionFreeKMS is generic: eta*rho=k • 1 implies
  k*weighted tau rho (x*y)=weighted tau rho (y*(rho*x*eta)).
  It does not assert an inverse. The CAR specialization derives its premise.
- Generator identities: a*omega(b*x)=c*omega(x*b),
  c*omega(B*x)=a*omega(x*B).
- occupation and vacuum readouts are a*tau(Bb), c*tau(bB).
  The commutator defect is (c-a)*tau(bB), since cyclicity equates the two
  support traces. Vacuum rho=bB has defect tau(bB), not automatically nonzero.
- tilted_vacuum_difference is a functional readout identity only.
- ann_mul_vacuum separately proves the actual operator equality b*(bB)=0.
  mixed_annihilator_vacuum proves
  (u*b1+v*B2)*(plus1*plus2)=v*(B2*(plus1*plus2)), with scalar actions
  understood. It does not assume off-site CAR, commuting supports, or that
  the right side is nonzero. Calling plus1*plus2 a joint projection would
  additionally require the appropriate support commutation hypothesis.

No blanket linter suppression is added. Scripts and imports have not been
elaborated for this candidate; warning cleanliness and axiom dependencies
remain unverified. No giant conjunction theorem or acceptance packet is added.

Excluded conclusions: positivity/normalization of weighted, faithful trace,
tracial iff equal weights without scalar cancellation, nonzero vacuum defect,
star preservation of arbitrary inner units, analytic KMS/Tomita, completed GNS
representation, and a reduced mixed state without an actual partial trace.
The existing NCG.KMSGNSCore isometry requires star preservation and functional
invariance; those premises are not supplied by algebraic covariance alone.
