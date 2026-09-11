import InfoGeometry.Canonical.CantorGoldenMeanBitwordBridge
import InfoGeometry.Algebra.FiniteSpinAlgebra
import InfoGeometry.OperatorAlgebra.AffineVirasoroBridge

/-!
# Automath / Cantor / exceptional compilation map

This file records the kernel-checked part of the cross-repository compilation
map suggested by the Automath golden-mean bitword architecture.

What is proved here:

* Automath-style golden-mean addresses are a subtype of the repo's full Cantor
  boundary.
* Their finite prefixes are finite no-adjacent-ones bitwords.
* The Boolean boundary is equivalent to the `plus/minus` Cuntz boundary used by
  the concrete `L2CantorCommutation` lane.
* The existing affine/Virasoro owner proves the level-one `E8` Sugawara central
  charge readout `c = 8`.

What is not proved here:

* No derivation of `E8(8)` from the Automath bitword system.
* No construction of the affine `E8` current representation on the Cantor
  Hilbert space.
* No Weyl integration, KMS trace, or analytic LCFT exchange-algebra theorem.
-/

noncomputable section

namespace InfoGeometry.Canonical.AutomathExceptionalCompilationMap

open InfoGeometry.Canonical.CantorGoldenMeanBitwordBridge
open InfoGeometry.OperatorAlgebra.AffineVirasoroBridge

/--
The verified cross-map from Automath-style bitwords to the repo's Cantor/Cuntz
boundary plus the existing level-one `E8` Sugawara readout.

This is a conjunction of owner facts, not a hidden theorem claiming that the
golden-mean shift constructs the exceptional current algebra.
-/
theorem goldenMeanCantorBoundary_e8_levelOne_compilation
    (x : GoldenMeanBoundary) (n : Nat) :
    NoAdjacentOnes x.1
      ∧ NoAdjacentFinite (prefixWord x.1 n)
      ∧ ofBaseIndex (toBaseIndex x.1) = x.1
      ∧ sugawaraCentralCharge 1 248 30 = 8 := by
  exact
    ⟨x.2,
      prefix_noAdjacentFinite x n,
      ofBaseIndex_toBaseIndex x.1,
      sugawaraCentralCharge_E8_levelOne⟩

/--
The zero-prepend branch preserves the Automath golden-mean subshift and
transports to the concrete Cuntz prepend operation under the Boolean
`false/true` ↔ `plus/minus` alphabet equivalence.
-/
theorem goldenMean_zeroPrepend_transports_to_cuntz
    (x : GoldenMeanBoundary) :
    NoAdjacentOnes (consBit false x.1)
      ∧ toBaseIndex (consBit false x.1) =
        InfoGeometry.Analysis.L2CantorCommutation.prepend
          (sectorOfBool false) (toBaseIndex x.1) := by
  exact
    ⟨noAdjacentOnes_cons_false x,
      toBaseIndex_consBit false x.1⟩

/--
The one-prepend branch preserves the Automath golden-mean subshift exactly when
the old head bit is zero, and it transports to the concrete Cuntz prepend
operation under the same alphabet equivalence.
-/
theorem goldenMean_onePrepend_transports_to_cuntz_of_head_false
    (x : GoldenMeanBoundary)
    (hhead : x.1 0 = false) :
    NoAdjacentOnes (consBit true x.1)
      ∧ toBaseIndex (consBit true x.1) =
        InfoGeometry.Analysis.L2CantorCommutation.prepend
          (sectorOfBool true) (toBaseIndex x.1) := by
  exact
    ⟨noAdjacentOnes_cons_true_of_head_false x hhead,
      toBaseIndex_consBit true x.1⟩

end InfoGeometry.Canonical.AutomathExceptionalCompilationMap
