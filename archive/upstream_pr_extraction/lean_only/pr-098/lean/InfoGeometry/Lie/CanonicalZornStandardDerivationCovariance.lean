import InfoGeometry.Lie.SplitOctonionStandardDerivation

/-!
# Covariance of canonical Zorn standard derivations

This is the concrete form of the standard-derivation covariance identity.
It is the algebraic interface used by root-bracket proofs; no coordinate
expansion of the Zorn product is involved.
-/

namespace InfoGeometry.Lie.CanonicalZornStandardDerivationCovariance

open InfoGeometry.Lie.CanonicalZornDerivation
open InfoGeometry.Lie.SplitOctonionStandardDerivation
open InfoGeometry.Algebra.Zorn.CanonicalVectorMatrixBridge

abbrev CZ := CanonicalZornDerivation.CZ
abbrev EndCZ := CanonicalZornDerivation.EndCZ

theorem standardDerivation_covariant
    (D : EndCZ) (hD : IsDerivation D) (a b x : CZ) :
    D (directCanonicalStanDerMap a b x) -
        directCanonicalStanDerMap a b (D x) =
      directCanonicalStanDerMap (D a) b x +
        directCanonicalStanDerMap a (D b) x := by
  change D (a * (b * x) - b * (a * x) +
      (a * (x * b) - (a * x) * b) +
      ((x * b) * a - (x * a) * b)) -
    (a * (b * D x) - b * (a * D x) +
      (a * (D x * b) - (a * D x) * b) +
      ((D x * b) * a - (D x * a) * b)) =
    ((D a) * (b * x) - b * ((D a) * x) +
      ((D a) * (x * b) - ((D a) * x) * b) +
      ((x * b) * (D a) - (x * (D a)) * b)) +
    (a * ((D b) * x) - (D b) * (a * x) +
      (a * (x * (D b)) - (a * x) * (D b)) +
      ((x * (D b)) * a - (x * a) * (D b)))
  change D (a * (b * x) - b * (a * x) +
      (a * (x * b) - (a * x) * b) +
      ((x * b) * a - (x * a) * b)) - _ = _
  rw [map_add, map_add, map_sub, map_sub, map_sub]
  repeat rw [hD]
  simp only [sub_eq_add_neg, add_mul, mul_add]
  abel

end InfoGeometry.Lie.CanonicalZornStandardDerivationCovariance
