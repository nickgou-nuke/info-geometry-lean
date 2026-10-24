/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import Mathlib.Tactic.NoncommRing

/-!
# Conditional chiral color-isospin projector identities

These polynomial identities are valid without commutation assumptions,
because their factors retain the fixed color-then-isospin ordering.
The names do not assert numerical ranks or a Spin(5,5) representation.
-/

namespace InfoGeometry.Physics.ColorIsospinProjectorSplit

variable {A : Type*} [Ring A]

def halfPlus (colorPos colorNeg pair iso : A) : A :=
  colorPos * pair + colorNeg * iso

def halfMinus (colorPos colorNeg pair iso : A) : A :=
  colorPos * iso + colorNeg * pair

/-- Partition of unity, given two actual partitions of unity. -/
theorem half_sum_eq_one
    (colorPos colorNeg pair iso : A)
    (hc : colorPos + colorNeg = 1)
    (hi : pair + iso = 1) :
    halfPlus colorPos colorNeg pair iso +
      halfMinus colorPos colorNeg pair iso = 1 := by
  calc
    halfPlus colorPos colorNeg pair iso +
        halfMinus colorPos colorNeg pair iso =
        (colorPos + colorNeg) * (pair + iso) := by
          unfold halfPlus halfMinus
          noncomm_ring
    _ = 1 := by rw [hc, hi, one_mul]

/-- Grading factorization requires no color-isospin commutativity. -/
theorem volume_factorization
    (colorPos colorNeg pair iso : A) :
    (colorPos - colorNeg) * (pair - iso) =
      halfPlus colorPos colorNeg pair iso -
        halfMinus colorPos colorNeg pair iso := by
  unfold halfPlus halfMinus
  noncomm_ring

/-- Four-sector expansion of the negative-chirality candidate. -/
theorem halfMinus_four_sector
    (baryon quark vacuum antiquark pair iso : A) :
    halfMinus (baryon + quark) (vacuum + antiquark) pair iso =
      baryon * iso + quark * iso + vacuum * pair + antiquark * pair := by
  unfold halfMinus
  noncomm_ring

end InfoGeometry.Physics.ColorIsospinProjectorSplit
