import Mathlib.Tactic
import InfoGeometry.Projective.Cl44QuaternionSplit

/-!
# Indefinite form on the doubled quaternionic carrier

The carrier is the repository-owned `SplitOctonion = Quaternion ℝ × Quaternion ℝ`.
The form is the real part of the quaternionic Hermitian pairing with a split
sign between the two Cayley--Dickson sectors.
-/

namespace InfoGeometry.Projective.QuaternionicMöbius

open InfoGeometry.Projective

noncomputable def quaternionRealInner (q r : Quaternion ℝ) : ℝ :=
  q.re * r.re + q.imI * r.imI + q.imJ * r.imJ + q.imK * r.imK

noncomputable def splitOctonionKreinForm
    (X Y : SplitOctonion) : ℝ :=
  quaternionRealInner X.q1 Y.q1 - quaternionRealInner X.q2 Y.q2

noncomputable def splitOctonionKreinQuadratic (X : SplitOctonion) : ℝ :=
  splitOctonionKreinForm X X

theorem splitOctonionKreinQuadratic_formula (X : SplitOctonion) :
    splitOctonionKreinQuadratic X =
      quaternionRealInner X.q1 X.q1 - quaternionRealInner X.q2 X.q2 := by
  rfl

theorem splitOctonion_pair_is_indefinite :
    splitOctonionKreinQuadratic { q1 := 1, q2 := 0 } = 1 ∧
    splitOctonionKreinQuadratic { q1 := 0, q2 := 1 } = -1 := by
  constructor <;> norm_num [splitOctonionKreinQuadratic,
    splitOctonionKreinForm, quaternionRealInner]

end InfoGeometry.Projective.QuaternionicMöbius
