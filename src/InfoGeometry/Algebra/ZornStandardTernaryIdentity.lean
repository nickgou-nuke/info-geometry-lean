/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.Algebra.ZornDerivationBridge
import InfoGeometry.Algebra.FiniteSpinAlgebra
import InfoGeometry.Lie.SplitOctonionStandardDerivationCovariance
import Mathlib.Tactic.NoncommRing

/-!
# Standard-derivation replacement for the associator bracket

Contract: use the existing standard derivation on ZornVectorMatrix over an
arbitrary commutative ring. Its ternary action satisfies the derivation form
of the fundamental identity. The raw associator is not substituted for this
operation, and total alternation is not asserted.
Dependency: alternative product → standard derivation → covariance → ternary identity.
-/
namespace InfoGeometry.Algebra

open InfoGeometry.Algebra.FiniteSpin

/-- Non-commutativity witness for the finite spin algebra carrier. -/
theorem exists_noncomm_pair :
    ∃ x y : Mat2C, x * y ≠ y * x :=
  ⟨J_plus, J_minus, j_plus_j_minus_ne⟩

section NonCommRingTernaryDerivation

variable {B : Type*} [Ring B]

/-- The Lie triple product `[u, v, w] = [[u, v], w] = (u * v - v * u) * w - w * (u * v - v * u)`
in any non-commutative associative ring `[Ring B]`. -/
def ringLieTriple (u v w : B) : B :=
  (u * v - v * u) * w - w * (u * v - v * u)

/-- In any non-commutative associative ring `[Ring B]`, the Lie triple product
`ringLieTriple a b` acts as a ternary derivation on `ringLieTriple u v w`:
`[a, b, [u, v, w]] = [[a, b, u], v, w] + [u, [a, b, v], w] + [u, v, [a, b, w]]`. -/
theorem ring_lie_triple_fundamental_identity (a b u v w : B) :
    ringLieTriple a b (ringLieTriple u v w) =
      ringLieTriple (ringLieTriple a b u) v w +
      ringLieTriple u (ringLieTriple a b v) w +
      ringLieTriple u v (ringLieTriple a b w) := by
  dsimp [ringLieTriple]
  noncomm_ring

end NonCommRingTernaryDerivation

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
