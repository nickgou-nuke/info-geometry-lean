import Mathlib.Algebra.Ring.Basic
import Mathlib.Tactic.NoncommRing

namespace InfoGeometry.Canonical.CoordinateFreeConnectionChannels

variable {A : Type u} [Ring A]
def commutator (X Y : A) : A := X * Y - Y * X

def twoSlotTorsionLeft (dEXY dEYX OX EY OY EX : A) : A :=
  dEXY - dEYX + OX * EY - OY * EX

def twoSlotTorsionComm (dEXY dEYX OX EY OY EX : A) : A :=
  dEXY - dEYX + commutator OX EY - commutator OY EX

structure ConnectionChannel {B : Type v} [Ring B] where
  map : A →+* B

variable {B : Type v} [Ring B] (ρ : ConnectionChannel (A := A) (B := B))

theorem map_twoSlotTorsionLeft (dEXY dEYX OX EY OY EX : A) :
    ρ.map (twoSlotTorsionLeft dEXY dEYX OX EY OY EX) =
      twoSlotTorsionLeft (ρ.map dEXY) (ρ.map dEYX) (ρ.map OX) (ρ.map EY) (ρ.map OY) (ρ.map EX) := by
  simp [twoSlotTorsionLeft]

theorem map_twoSlotTorsionComm (dEXY dEYX OX EY OY EX : A) :
    ρ.map (twoSlotTorsionComm dEXY dEYX OX EY OY EX) =
      twoSlotTorsionComm (ρ.map dEXY) (ρ.map dEYX) (ρ.map OX) (ρ.map EY) (ρ.map OY) (ρ.map EX) := by
  simp [twoSlotTorsionComm, commutator]

end InfoGeometry.Canonical.CoordinateFreeConnectionChannels
