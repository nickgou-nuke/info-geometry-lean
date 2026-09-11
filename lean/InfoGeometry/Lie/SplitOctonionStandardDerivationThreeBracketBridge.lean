import InfoGeometry.Lie.SplitOctonionStandardDerivation
import InfoGeometry.Algebra.FiniteSpinAlgebra

/-!
# Ternary bracket induced by the standard split-octonion derivation

This is a thin consumer of the concrete canonical Zorn derivation owner.  It
records the honest operator-level consequence of the standard derivation
construction: a binary-labelled derivation acts as a ternary operation.

No claim about a general graded Lie-3 algebra, Malcev structure, or a braid
representation is made here.  Those require additional identities and belong
to separate owners.
-/

noncomputable section

namespace InfoGeometry.Lie.SplitOctonionStandardDerivationThreeBracketBridge

open InfoGeometry.Lie.CanonicalZornDerivation
open InfoGeometry.Lie.SplitOctonionStandardDerivation

abbrev CZ := CanonicalZornDerivation.CZ

/-- The ternary operation induced by Baez's standard derivation. -/
def splitThreeBracket (x y z : CZ) : CZ :=
  (canonicalStandardDerivationOfCanonical x y).1 z

@[simp] theorem splitThreeBracket_eq_standardDerivation_apply
    (x y z : CZ) :
    splitThreeBracket x y z =
      (canonicalStandardDerivationOfCanonical x y).1 z := rfl

/-- The ternary operation is a derivation in its third argument. -/
theorem splitThreeBracket_derivation
    (x y a b : CZ) :
    splitThreeBracket x y (a * b) =
      splitThreeBracket x y a * b + a * splitThreeBracket x y b := by
  exact (canonicalStandardDerivationOfCanonical x y).property a b

/-- The bracket is additive in the acted-on argument. -/
theorem splitThreeBracket_add_right
    (x y a b : CZ) :
    splitThreeBracket x y (a + b) =
      splitThreeBracket x y a + splitThreeBracket x y b := by
  exact (canonicalStandardDerivationOfCanonical x y).1.map_add a b

/-- The bracket is real-linear in the acted-on argument. -/
theorem splitThreeBracket_smul_right
    (r : ℝ) (x y a : CZ) :
    splitThreeBracket x y (r • a) = r • splitThreeBracket x y a := by
  exact (canonicalStandardDerivationOfCanonical x y).1.map_smul r a

end InfoGeometry.Lie.SplitOctonionStandardDerivationThreeBracketBridge
