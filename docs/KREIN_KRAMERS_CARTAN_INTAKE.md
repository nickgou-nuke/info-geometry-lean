# Krein–Kramers–Hestenes–Cartan intake

Source: user-supplied five-stage hierarchy and proposed
`KreinKramersHestenesCartanAnomaly.lean`, 2026-10-23. This record preserves
the atomic claims and their corrections; the pasted code is not accepted
as compiler evidence. The broader counterexample-realignment goal remains open.

## Ground-truth contract and owner map

* Carrier for the new algebraic delta: any `Carrier` with `Ring` and
  `StarRing`; multiplication is ring multiplication, not opposite composition.
* `Krein.StarHomAdjointTransport.conjugate_star_mul` and
  `conjugate_star_involutive` already prove the twisted-star laws using
  `Krein.TwoSheetKreinIdealBridge.kreinConjugate`.
* `Krein.TwoSheetKreinIdealBridge.kreinConjugate_mul` proves that
  `J * (X * Y) * J = (J * X * J) * (J * Y * J)` when `J * J = 1`.
  The intake reverses this order incorrectly. A star or an explicit
  opposite-ring representation is required for an order-reversing map.
* `Canonical.HestenesKramersBridge.inner_first_second_eq_zero` gives genuine
  real Hilbert orthogonality for the native doubled-space phase partner.
  `kreinInner_phasePartner_phasePartner` proves its full sign-reversed pairing.
  The arbitrary-ring equation `X* T X + (T X)* X = 0` only cancels the
  symmetrized pairing; it does not say either summand is zero.
* The new generic lemmas in `Krein.StarHomAdjointTransport` derive
  `star T = -T` from `star T * T = 1` and `T * T = -1`, and derive
  `star (T * X) * J * (T * Y) = -(star X * J * Y)` directly from
  `star T * T = 1` and `J * T = -(T * J)`.
  Neither self-adjointness of `J` nor `T * T = -1` is needed for the latter.
  No new bundled hypothesis structure or surrogate state carrier is introduced.
* `Canonical.CertifiedInverseKernel` already contains
  `spectralProjector_commutator_GammaG_eq_sub_anomalies` and spectral oddness
  of both anomalies. `Canonical.CartanDecomposition` owns the spectral
  involution and grading commutator. Their existing conventions must be kept.

## Interpretation boundaries and remaining review

* A sign reversal can pair two null values; “strictly opposite signatures”
  requires a nonzero scalar-valued quadratic readout and an ordering.
* An element of a star ring is not automatically an antiunitary map.
  The complex antiunitary and real internal-complex carriers remain distinct.
* A centralizer in a bare star ring is a star subring. Calling it an algebra
  requires a scalar algebra structure and scalar-closure proof.
* The integer example supplies an oblique idempotent and a left projection,
  not the full claimed Moore–Penrose pair or right anomaly. The right projector
  with halves must be realized over an appropriate scalar field; multiplying
  a projection by two does not preserve idempotence in general.
* Nonzero anomaly commutators describe failure to commute, not a proved
  geometric apex singularity. The abstract claims do not prove an ordered
  indefinite metric theorem, standard-form representation, or physical model.

OpenGauss Gate 0 discovery and direct owner inspection were performed.
Independent A-A and QA-A reviews have not run: this session exposes no native
agent-spawning API. Author checks and kernel output must not be reported as
independent OpenGauss acceptance. Remaining intake atoms require owner-by-owner
review; no five-stage closure is claimed.

## Current verification and concurrent work

The locked `InfoGeometry.Krein.StarHomAdjointTransportAudit` build passed;
each of the four new lemmas depends only on `propext`. The owner retains
pre-existing unused-section-variable warnings. The static OpenGauss screener
and strict refutation scan reported zero traps. The semantic-vacuity heuristic
flagged three pre-existing simplification lemmas, none of the new lemmas.

During this work, concurrent commits `f70a165de` and `2b6bd0671` added
`Canonical.KreinKramersAlternatives` and `Canonical.DrazinCartanAlternatives`.
Their source was inspected after arrival; their bundled Kramers quadratic
specialization overlaps the generic transport law above. This is not new
independent coverage. Consolidating those surfaces requires a separate
dependency review and coordination with their active writer. No independent
review or build verdict for those commits is asserted here.
