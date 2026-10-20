/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/

import InfoGeometry.Topology.KleinQuotientDeckInvariants

namespace InfoGeometry.Topology.KleinQuotientDeckInvariants.KleinDeckGroup

open InfoGeometry.Topology.KleinQuotientDeckInvariants

theorem mul_right_inv (g : KleinDeckGroup) :
    mul g (inv g) = one := by
  rcases g with ⟨m, n⟩
  simp only [mul, inv, one]
  have hs : signZ n * signZ n = 1 := by
    have h : signZ n = 1 ∨ signZ n = -1 := by
      simp [signZ]
      omega
    rcases h with h | h <;> simp [h]
  congr 1
  · calc
      m + signZ n * (-signZ n * m) = m - (signZ n * signZ n) * m := by ring
      _ = 0 := by rw [hs]; ring
  · ring

end InfoGeometry.Topology.KleinQuotientDeckInvariants.KleinDeckGroup
