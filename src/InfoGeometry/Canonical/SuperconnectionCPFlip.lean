import InfoGeometry.Canonical.SuperconnectionZornBianchiBridge
import InfoGeometry.Krein.KreinSpace
import Mathlib.Data.Real.Basic

namespace InfoGeometry.Canonical.Superconnection

open InfoGeometry.Krein

/-- The formal CP flip (Tomita reflection) on the 5-graded Maurer-Cartan superconnection.
This operation inverts the chiral grades and applies the Krein space modular conjugation `jCLM`. -/
noncomputable def cpFlip {H : Type*} [NonUnitalNonAssocRing H] [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H] [KreinSpace H] (w : NonAssocGradedMaurerCartanForm H) : NonAssocGradedMaurerCartanForm H where
  w_n2 := KreinSpace.jCLM w.w_p2
  w_n1 := KreinSpace.jCLM w.w_p1
  w_0  := KreinSpace.jCLM w.w_0
  w_p1 := KreinSpace.jCLM w.w_n1
  w_p2 := KreinSpace.jCLM w.w_n2

/-- The CP flip is a perfect involution on the superconnection. -/
theorem cpFlip_involutive {H : Type*} [NonUnitalNonAssocRing H] [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H] [KreinSpace H] (w : NonAssocGradedMaurerCartanForm H) :
    cpFlip (cpFlip w) = w := by
  cases w
  dsimp [cpFlip]
  congr <;> simp [KreinSpace.jCLM_apply, KreinSpace.J_invol]

end InfoGeometry.Canonical.Superconnection
