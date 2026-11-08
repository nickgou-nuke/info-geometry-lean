/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.Lie.SplitOctonionStandardDerivationThreeBracketBridge
import InfoGeometry.Lie.CanonicalZornStandardDerivationCovariance

/-! The standard-derivation ternary operation satisfies the derivation form
of the fundamental identity. This is a constructive replacement for applying
that identity to the raw octonion associator. Total alternation is not asserted. -/

namespace InfoGeometry.Lie.SplitOctonionStandardDerivationThreeBracketBridge

open InfoGeometry.Lie.CanonicalZornDerivation
open InfoGeometry.Lie.SplitOctonionStandardDerivation
open InfoGeometry.Lie.CanonicalZornStandardDerivationCovariance

/-- Every native derivation acts on all three arguments of the existing bracket. -/
theorem splitThreeBracket_covariant (D : CanonicalZornDerivation.EndCZ)
    (hD : IsDerivation D)
    (u v w : CZ) :
    D (splitThreeBracket u v w) =
      splitThreeBracket (D u) v w + splitThreeBracket u (D v) w +
        splitThreeBracket u v (D w) := by
  have h := standardDerivation_covariant D hD u v w
  change D (splitThreeBracket u v w) - splitThreeBracket u v (D w) =
    splitThreeBracket (D u) v w + splitThreeBracket u (D v) w at h
  exact sub_eq_iff_eq_add.mp h

/-- Standard-derivation brackets obey the ternary derivation identity on the
same split-octonion carrier, without a Filippov alternation claim. -/
theorem splitThreeBracket_fundamental_identity (x y u v w : CZ) :
    splitThreeBracket x y (splitThreeBracket u v w) =
      splitThreeBracket (splitThreeBracket x y u) v w +
      splitThreeBracket u (splitThreeBracket x y v) w +
      splitThreeBracket u v (splitThreeBracket x y w) := by
  exact splitThreeBracket_covariant
    (canonicalStandardDerivationOfCanonical x y).1
    (canonicalStandardDerivationOfCanonical x y).property u v w

end InfoGeometry.Lie.SplitOctonionStandardDerivationThreeBracketBridge
