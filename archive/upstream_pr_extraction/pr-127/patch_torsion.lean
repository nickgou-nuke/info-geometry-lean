import Mathlib.Algebra.Ring.Basic
import Mathlib.Tactic.NoncommRing

namespace InfoGeometry.Canonical.CoordinateFreeConnectionChannels

variable {A : Type u} [Ring A]

/-- Associative-ring commutator, used as the coordinate-free Lie bracket. -/
def commutator (X Y : A) : A :=
  X * Y - Y * X

/--
Two-slot torsion expression (left action).

This is the finite algebraic shadow of `T = dE + \Omega \wedge E`: the derivative part
is represented by `dEXY - dEYX`, and the connection action by `OX * EY - OY * EX`.
-/
def twoSlotTorsionLeft (dEXY dEYX OX EY OY EX : A) : A :=
  dEXY - dEYX + OX * EY - OY * EX

/--
Two-slot torsion expression (commutator action).

This is the shadow of `T = dE + [\Omega, E]_\wedge`.
-/
def twoSlotTorsionComm (dEXY dEYX OX EY OY EX : A) : A :=
  dEXY - dEYX + commutator OX EY - commutator OY EX

/-- Torsion is antisymmetric in its two slots (left action). -/
theorem twoSlotTorsionLeft_swap (dEXY dEYX OX EY OY EX : A) :
    twoSlotTorsionLeft dEYX dEXY OY EX OX EY = -twoSlotTorsionLeft dEXY dEYX OX EY OY EX := by
  unfold twoSlotTorsionLeft
  noncomm_ring

/-- Torsion is antisymmetric in its two slots (commutator action). -/
theorem twoSlotTorsionComm_swap (dEXY dEYX OX EY OY EX : A) :
    twoSlotTorsionComm dEYX dEXY OY EX OX EY = -twoSlotTorsionComm dEXY dEYX OX EY OY EX := by
  unfold twoSlotTorsionComm commutator
  noncomm_ring

end InfoGeometry.Canonical.CoordinateFreeConnectionChannels
