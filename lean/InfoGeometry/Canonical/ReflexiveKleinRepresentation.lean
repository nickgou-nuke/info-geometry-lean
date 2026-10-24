/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.Canonical.ReflexiveFlowUnits
import InfoGeometry.Canonical.KleinPresentedGroup

/-! A representation of the existing algebraically presented Klein group in
units of a noncommutative ring. No faithfulness or topological identification
is asserted. The inverted generator is the multiplicative flow, not its
infinitesimal grading. -/
namespace InfoGeometry.Canonical.ReflexiveNilpotentFlows
open KleinPresentedGroup
variable {R A : Type*} [CommRing R] [Ring A] [Algebra R A]
variable {d B : A} (hd : d * d = 0) (hB : B * B = 0)
  (hr : d * B * d = d) (hs : B * d * B = B)

def reflexiveKleinRep (t : Rˣ) : KleinGroup →* Aˣ :=
  kleinRep (weylUnit hd hB hr) (diagonalUnit hd hB hr hs t)
    (weylUnit_conjugates_diagonalUnit hd hB hr hs t)

@[simp] theorem reflexiveKleinRep_genA (t : Rˣ) :
    reflexiveKleinRep hd hB hr hs t (toKlein genA) = weylUnit hd hB hr :=
  (kleinRep_relator_relation _ _
    (weylUnit_conjugates_diagonalUnit hd hB hr hs t)).1

@[simp] theorem reflexiveKleinRep_genB (t : Rˣ) :
    reflexiveKleinRep hd hB hr hs t (toKlein genB) = diagonalUnit hd hB hr hs t :=
  (kleinRep_relator_relation _ _
    (weylUnit_conjugates_diagonalUnit hd hB hr hs t)).2

theorem reflexiveKleinRep_genA_fourth (t : Rˣ) :
    reflexiveKleinRep hd hB hr hs t ((toKlein genA) ^ 4) = 1 := by
  rw [map_pow, reflexiveKleinRep_genA]
  apply Units.ext
  change weyl d B ^ 4 = 1
  exact weyl_fourth hd hB hr hs

end InfoGeometry.Canonical.ReflexiveNilpotentFlows
