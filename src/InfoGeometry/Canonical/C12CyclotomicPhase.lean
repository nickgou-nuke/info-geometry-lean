import Mathlib.Data.ZMod.Basic
import InfoGeometry.Algebra.FiniteSpinAlgebra
import Mathlib.Tactic

/-!
# Twelve-fold cyclotomic phase labels

This owner records the finite cyclic `ZMod 12` phase action and its quotient
to the existing six-mode label carrier.  The order-six element is a genuine
nontrivial half-turn on `ZMod 12`, but it is killed by the quotient to
`ZMod 6`.  Consequently the existing six circular Zorn channels cannot test a
nontrivial multiplicative lift of this half-turn; such a test requires a
concrete twelve-channel carrier.

No dihedral, glide, Klein-bottle, or split-octonion automorphism claim is made.
-/

namespace InfoGeometry.Canonical.C12CyclotomicPhase

/-- The native twelve-fold finite phase-label carrier. -/
abbrev C12Index := ZMod 12

/-- The existing six-mode label carrier, displayed as the quotient of `C12`. -/
abbrev C6Index := ZMod 6

/-- Translation by a twelve-fold phase label. -/
def rotation (k : C12Index) : C12Index ≃ C12Index :=
  Equiv.addRight k

@[simp] theorem rotation_apply (k n : C12Index) :
    rotation k n = n + k := rfl

theorem rotation_add (k l : C12Index) :
    rotation (k + l) = rotation k ∘ rotation l := by
  ext n
  simp [rotation, add_comm, add_left_comm]

/-- Twelve unit steps act trivially. -/
theorem rotation_twelve :
    rotation (12 : C12Index) = Equiv.refl C12Index := by
  decide

/-- The order-six element is still nontrivial on the twelve-fold carrier. -/
theorem halfTurn_nontrivial :
    rotation (6 : C12Index) ≠ Equiv.refl C12Index := by
  decide

theorem card_c12 : Fintype.card C12Index = 12 :=
  ZMod.card 12

/-- Quotient the twelve-fold phase labels to the existing six-mode labels. -/
def toSixMode : C12Index →+ C6Index :=
  (ZMod.castHom (by norm_num : 6 ∣ 12) (ZMod 6)).toAddMonoidHom

@[simp] theorem toSixMode_add (m n : C12Index) :
    toSixMode (m + n) = toSixMode m + toSixMode n :=
  map_add toSixMode m n

/-- The half-turn lies in the kernel of the six-mode quotient. -/
theorem toSixMode_halfTurn :
    toSixMode (6 : C12Index) = 0 := by
  decide

/-- Hence the current six-channel readout cannot distinguish the half-turn
from the identity. -/
theorem toSixMode_halfTurn_add (n : C12Index) :
    toSixMode (n + 6) = toSixMode n := by
  rw [toSixMode_add, toSixMode_halfTurn, add_zero]

end InfoGeometry.Canonical.C12CyclotomicPhase
