/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import Mathlib.Algebra.Group.End
import Mathlib.Algebra.Group.Commute.Basic
import Mathlib.Tactic.Group

/-!
# Nonabelian transition defects

An arbitrary group-valued transition assignment has a conjugated tetrahedral
identity. Ordinary untwisted cocycle identities require the displayed
commutation hypothesis. No cover, gerbe, or scalar multiplier is assumed.
-/

namespace InfoGeometry.Cocycle.TransitionDefect

variable {I G : Type*} [Group G]

/-- Failure of the ordered transition composition to equal the direct transition. -/
def transitionDefect (ψ : I → I → G) (i j k : I) : G :=
  ψ i j * ψ j k * (ψ i k)⁻¹

theorem transitionDefect_mul (ψ : I → I → G) (i j k : I) :
    transitionDefect ψ i j k * ψ i k = ψ i j * ψ j k := by
  simp [transitionDefect, mul_assoc]

theorem transitionDefect_eq_one_iff (ψ : I → I → G) (i j k : I) :
    transitionDefect ψ i j k = 1 ↔ ψ i j * ψ j k = ψ i k := by
  constructor
  · intro h
    simpa [h] using (transitionDefect_mul ψ i j k).symm
  · intro h
    simp [transitionDefect, h]

/-- Associativity produces conjugation of the defect based at the next vertex. -/
theorem transitionDefect_tetrahedral (ψ : I → I → G) (i j k l : I) :
    transitionDefect ψ i j k * transitionDefect ψ i k l =
      MulAut.conj (ψ i j) (transitionDefect ψ j k l) *
        transitionDefect ψ i j l := by
  simp only [transitionDefect, MulAut.conj_apply]
  group

/-- Changing a frame at each vertex acts on an ordered transition. -/
def changeFrames (ψ : I → I → G) (g : I → G) (i j : I) : G :=
  g i * ψ i j * (g j)⁻¹

/-- The full defect transforms by conjugation, not by equality in general. -/
theorem transitionDefect_changeFrames (ψ : I → I → G) (g : I → G) (i j k : I) :
    transitionDefect (changeFrames ψ g) i j k =
      MulAut.conj (g i) (transitionDefect ψ i j k) := by
  simp only [transitionDefect, changeFrames, MulAut.conj_apply]
  group

theorem changeFrames_comp (ψ : I → I → G) (g h : I → G) :
    changeFrames (changeFrames ψ g) h = changeFrames ψ (fun i => h i * g i) := by
  funext i j
  simp only [changeFrames]
  group

/-- Commutation with the intervening transition removes the conjugation. -/
theorem transitionDefect_tetrahedral_of_commute
    (ψ : I → I → G) (i j k l : I)
    (h : Commute (ψ i j) (transitionDefect ψ j k l)) :
    transitionDefect ψ i j k * transitionDefect ψ i k l =
      transitionDefect ψ j k l * transitionDefect ψ i j l := by
  rw [transitionDefect_tetrahedral, MulAut.conj_apply, h.eq]
  simp [mul_assoc]

end InfoGeometry.Cocycle.TransitionDefect
