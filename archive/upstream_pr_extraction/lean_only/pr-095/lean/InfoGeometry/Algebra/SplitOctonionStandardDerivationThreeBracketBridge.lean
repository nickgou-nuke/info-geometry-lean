import InfoGeometry.Algebra.BaezG2AlternativeDerivations

/-!
# Split-octonion ternary bracket from standard derivations

The binary split-octonion product already has a native Baez standard
derivation `D_{x,y}`.  This thin owner exposes the induced ternary operation
`[x,y,z]₃ := D_{x,y}(z)` without introducing a second multiplication or a
new abstract derivation axiom.  Only consequences of the kernel-checked
Leibniz theorem are recorded here.
-/

noncomputable section

namespace InfoGeometry.Algebra.SplitOctonionStandardDerivationThreeBracketBridge

open InfoGeometry.Algebra
open InfoGeometry.Canonical.ZornVectorMatrixExplicit.KingdonSplitOctonion

/-- The ternary operation induced by the native split-octonion derivation. -/
def splitThreeBracket (x y z : AbstractKingdon) : AbstractKingdon :=
  baezSplitDerivation x y z

@[simp] theorem splitThreeBracket_eq_standard_formula
    (x y z : AbstractKingdon) :
    splitThreeBracket x y z =
      (x * y - y * x) * z - z * (x * y - y * x) -
        (3 : ℕ) • associator x y z := by
  exact baezSplitDerivation_apply x y z

/-- The ternary bracket is a derivation in its third slot. -/
theorem splitThreeBracket_leibniz
    (x y a b : AbstractKingdon) :
    splitThreeBracket x y (a * b) =
      splitThreeBracket x y a * b + a * splitThreeBracket x y b := by
  exact NonAssocDerivation.leibniz (baezSplitDerivation x y) a b

@[simp] theorem splitThreeBracket_zero_left (y z : AbstractKingdon) :
    splitThreeBracket 0 y z = 0 := by
  simp [splitThreeBracket, baezSplitDerivation, associator]

@[simp] theorem splitThreeBracket_zero_middle (x z : AbstractKingdon) :
    splitThreeBracket x 0 z = 0 := by
  simp [splitThreeBracket, baezSplitDerivation, associator]

end InfoGeometry.Algebra.SplitOctonionStandardDerivationThreeBracketBridge
