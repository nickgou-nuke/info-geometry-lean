import InfoGeometry.Projective.Cl44QuaternionSplit
import InfoGeometry.Algebra.FiniteSpinAlgebra
import InfoGeometry.OperatorAlgebra.RealDoubledChiralKrein
import Mathlib.Analysis.Normed.Algebra.QuaternionExponential

noncomputable section

namespace InfoGeometry.Projective.QuaternionicMöbius

open InfoGeometry.Projective
open InfoGeometry.Krein
open InfoGeometry.OperatorAlgebra.RealDoubledChiralKrein

abbrev QuaternionicKreinCarrier :=
  DoubledSpace (Quaternion ℝ)

noncomputable def splitOctonionToDoubled
    (X : SplitOctonion) : QuaternionicKreinCarrier :=
  to_doubled X.q1 X.q2

noncomputable def doubledToSplitOctonion
    (u : QuaternionicKreinCarrier) : SplitOctonion :=
  { q1 := WithLp.fst u, q2 := WithLp.snd u }

@[simp] theorem doubledToSplit_toDoubled (X : SplitOctonion) :
    doubledToSplitOctonion (splitOctonionToDoubled X) = X := by
  cases X
  rfl

@[simp] theorem toDoubled_doubledToSplit (u : QuaternionicKreinCarrier) :
    splitOctonionToDoubled (doubledToSplitOctonion u) = u := by
  apply DoubledSpace.ext <;> rfl

theorem splitOctonion_splitKreinForm_readback
    (X Y : SplitOctonion) :
    splitKreinForm (E := Quaternion ℝ)
        (splitOctonionToDoubled X) (splitOctonionToDoubled Y) =
      inner ℝ X.q1 Y.q1 - inner ℝ X.q2 Y.q2 := by
  rfl

theorem splitOctonion_fundamentalSymmetry_readback
    (X : SplitOctonion) :
    spectral_epsilon (E := Quaternion ℝ)
        (splitOctonionToDoubled X) =
      splitOctonionToDoubled { q1 := X.q1, q2 := -X.q2 } := by
  rfl

end InfoGeometry.Projective.QuaternionicMöbius
