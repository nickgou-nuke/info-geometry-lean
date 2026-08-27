/- SPDX-License-Identifier: Apache-2.0 -/

import Mathlib

/-!
# The Artin--Schreier polynomial over `𝔽₂`

This owner records the concrete characteristic-two polynomial only.  It does
not identify it with any G₂ peeling coordinate.
-/

namespace InfoGeometry.Physics.Algebra.ArtinSchreierF2

def artinSchreier (x : ZMod 2) : ZMod 2 := x ^ 2 - x

def artinSchreierHom : ZMod 2 →+ ZMod 2 where
  toFun := artinSchreier
  map_zero' := by simp [artinSchreier]
  map_add' := by
    intro x y
    fin_cases x <;> fin_cases y <;> decide

theorem artinSchreier_eq_zero (x : ZMod 2) :
    artinSchreier x = 0 := by
  fin_cases x <;> decide

theorem artinSchreier_equation_exists_iff (a : ZMod 2) :
    (∃ x : ZMod 2, artinSchreier x = a) ↔ a = 0 := by
  constructor
  · rintro ⟨x, hx⟩
    rw [artinSchreier_eq_zero x] at hx
    exact hx.symm
  · intro ha
    exact ⟨0, by simp [ha, artinSchreier]⟩

end InfoGeometry.Physics.Algebra.ArtinSchreierF2
