import InfoGeometry.Canonical.ErlangenTwistorGromovGrothendieckBridge

namespace InfoGeometry.Canonical.ErlangenTwistorGromovGrothendieckCapstone

open InfoGeometry.Canonical.ErlangenTwistorMasterBridge
open InfoGeometry.Ergodic.RuelleTransfer

/-- The four component identities supplied by the Erlangen--twistor bridge.

This is a packaging theorem only: the Plücker relation, null-twistor relation,
BPS Weyl normalization, and unweighted transfer count are proved by their
respective carrier owners. -/
theorem master_geometric_diamond_canonical_capstone
    (K : KleinQuadricPlucker)
    (T : PenroseNullTwistor)
    (W : WeylGaugeScaleDatum)
    (n : ℕ) (x : BitWord n) :
    (K.p01 * K.p23 + K.p02 * K.p31 + K.p03 * K.p12 = 0) ∧
    ((T.omega.1 * star T.pi.1 + T.omega.2 * star T.pi.2).re = 0) ∧
    (weylConformalFactor W = 1) ∧
    (gromovWittenPartitionFunction (fun _ => 0) x = 2) := by
  exact ⟨K.klein_quadratic_relation, T.null_norm,
    weyl_conformal_factor_bps_eq_one W,
    gromov_witten_unweighted_eq_two x⟩

end InfoGeometry.Canonical.ErlangenTwistorGromovGrothendieckCapstone
