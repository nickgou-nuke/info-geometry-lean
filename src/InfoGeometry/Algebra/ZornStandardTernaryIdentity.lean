import InfoGeometry.Algebra.ZornDerivationBridge
import InfoGeometry.Lie.SplitOctonionStandardDerivationCovariance

/-!
# Standard-derivation replacement for the associator bracket

Contract: use the existing standard derivation on ZornVectorMatrix over an
arbitrary commutative ring. Its ternary action satisfies the derivation form
of the fundamental identity. The raw associator is not substituted for this
operation, and total alternation is not asserted.
Dependency: alternative product → standard derivation → covariance → ternary identity.
-/
namespace InfoGeometry.Algebra

variable {R : Type*} [CommRing R]

theorem zorn_standard_ternary_fundamental_identity
    (a b u v w : ZornVectorMatrix R) :
    zornStanDerivation a b (zornStanDerivation u v w) =
      zornStanDerivation (zornStanDerivation a b u) v w +
      zornStanDerivation u (zornStanDerivation a b v) w +
      zornStanDerivation u v (zornStanDerivation a b w) := by
  have h := (zornStanDerivation a b).stanDerMap_covariant u v w
  change zornStanDerivation a b (zornStanDerivation u v w) -
      zornStanDerivation u v (zornStanDerivation a b w) =
      zornStanDerivation (zornStanDerivation a b u) v w +
      zornStanDerivation u (zornStanDerivation a b v) w at h
  exact sub_eq_iff_eq_add.mp h

end InfoGeometry.Algebra
