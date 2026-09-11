import InfoGeometry.Lie.SplitRealNullTetradZornBridge
import InfoGeometry.Algebra.FiniteSpinAlgebra
import InfoGeometry.Lie.SplitOctonionCircularReciprocalExponentialBridge

/-!
# Reciprocal exponential readout of the split `(2,2)` tetrad boost

The native split-real double-Witt boost and the circular reciprocal pair are
the same eigenvalue data on the two chosen null directions.  This file only
packages that already-proved comparison; it makes no new multiplication,
automorphism, or causal-boundary claim.
-/

noncomputable section

namespace InfoGeometry.Lie.SplitOctonionCircularReciprocalTetradBridge

open InfoGeometry.Lie.SplitRealNullTetradZornBridge
open InfoGeometry.Lie.SplitRealNullTetradZornBridge.Tetrad
open InfoGeometry.Lie.SplitOctonionCircularReciprocalExponentialBridge
open InfoGeometry.Clifford.SplitRealNullTetrad

theorem doubleWittBoost_causalPair_eq_reciprocalExponentialPair (t : ℝ) :
    doubleWittBoost t InfoGeometry.Clifford.SplitRealNullTetrad.causalMinus =
        (reciprocalExponentialPair t).1 •
          InfoGeometry.Clifford.SplitRealNullTetrad.causalMinus ∧
      doubleWittBoost t InfoGeometry.Clifford.SplitRealNullTetrad.causalPlus =
        (reciprocalExponentialPair t).2 •
          InfoGeometry.Clifford.SplitRealNullTetrad.causalPlus := by
  constructor
  · simpa only [reciprocalExponentialPair_fst] using
      (doubleWittBoost_causalMinus t)
  · simpa only [reciprocalExponentialPair_snd] using
      (doubleWittBoost_causalPlus t)

theorem doubleWittBoost_entropyPair_eq_reciprocalExponentialPair (t : ℝ) :
    doubleWittBoost t InfoGeometry.Clifford.SplitRealNullTetrad.entropyMinus =
        (reciprocalExponentialPair t).1 •
          InfoGeometry.Clifford.SplitRealNullTetrad.entropyMinus ∧
      doubleWittBoost t InfoGeometry.Clifford.SplitRealNullTetrad.entropyPlus =
        (reciprocalExponentialPair t).2 •
          InfoGeometry.Clifford.SplitRealNullTetrad.entropyPlus := by
  constructor
  · simpa only [reciprocalExponentialPair_fst] using
      (doubleWittBoost_entropyMinus t)
  · simpa only [reciprocalExponentialPair_snd] using
      (doubleWittBoost_entropyPlus t)

end InfoGeometry.Lie.SplitOctonionCircularReciprocalTetradBridge
