/- SPDX-License-Identifier: Apache-2.0 -/

import InfoGeometry.Algebra.Zorn.G2CoordinateWordActionBridge
import InfoGeometry.Algebra.FiniteSpinAlgebra

/-!
# Weyl-invariant Cartan coordinates

This owner records the polynomial invariants of the native integer Cartan
coordinate carrier.  It is deliberately independent of the finite quotient
exhaustion theorem and does not claim that equal invariant values classify
regular Weyl orbits.
-/

namespace InfoGeometry.Algebra.Zorn.G2CartanCasimirCoordinates

open InfoGeometry.Algebra.Zorn.G2CoordinateWordActionBridge
open InfoGeometry.Algebra.Zorn.G2CoordinateWeylAction
open InfoGeometry.Algebra.Zorn.G2Roots

def cartanQuadratic (v : ℤ × ℤ) : ℤ :=
  v.1 ^ 2 - 3 * v.1 * v.2 + 3 * v.2 ^ 2

def cartanSextic (v : ℤ × ℤ) : ℤ :=
  v.2 ^ 2 * (v.1 - v.2) ^ 2 * (v.1 - 2 * v.2) ^ 2

def cartanCasimirCoordinate (v : ℤ × ℤ) : ℤ × ℤ :=
  (cartanQuadratic v, cartanSextic v)

def cartanCasimirLevelSet (v₀ : ℤ × ℤ) : Set (ℤ × ℤ) :=
  {v | cartanCasimirCoordinate v = cartanCasimirCoordinate v₀}

theorem cartanQuadratic_s1 (v : ℤ × ℤ) :
    cartanQuadratic (s1 v) = cartanQuadratic v := by
  rcases v with ⟨a, b⟩
  simp [cartanQuadratic, s1]
  ring

theorem cartanQuadratic_s2 (v : ℤ × ℤ) :
    cartanQuadratic (s2 v) = cartanQuadratic v := by
  rcases v with ⟨a, b⟩
  simp [cartanQuadratic, s2]
  ring

theorem cartanSextic_s1 (v : ℤ × ℤ) :
    cartanSextic (s1 v) = cartanSextic v := by
  rcases v with ⟨a, b⟩
  simp [cartanSextic, s1]
  ring

theorem cartanSextic_s2 (v : ℤ × ℤ) :
    cartanSextic (s2 v) = cartanSextic v := by
  rcases v with ⟨a, b⟩
  simp [cartanSextic, s2]
  ring

theorem cartanQuadratic_coordinateWordAction
    (word : List Bool) (α : G2CoordinateRoot) :
    cartanQuadratic ((coordinateWordAction word α).1) =
      cartanQuadratic α.1 := by
  induction word generalizing α with
  | nil => rfl
  | cons bit word ih =>
      simp only [coordinateWordAction, Equiv.trans_apply]
      by_cases hbit : bit
      · simp only [if_pos hbit]
        rw [ih]
        exact cartanQuadratic_s1 α.1
      · simp only [if_neg hbit]
        rw [ih]
        exact cartanQuadratic_s2 α.1

theorem cartanSextic_coordinateWordAction
    (word : List Bool) (α : G2CoordinateRoot) :
    cartanSextic ((coordinateWordAction word α).1) =
      cartanSextic α.1 := by
  induction word generalizing α with
  | nil => rfl
  | cons bit word ih =>
      simp only [coordinateWordAction, Equiv.trans_apply]
      by_cases hbit : bit
      · simp only [if_pos hbit]
        rw [ih]
        exact cartanSextic_s1 α.1
      · simp only [if_neg hbit]
        rw [ih]
        exact cartanSextic_s2 α.1

theorem cartanCasimirCoordinate_coordinateWordAction
    (word : List Bool) (α : G2CoordinateRoot) :
    cartanCasimirCoordinate ((coordinateWordAction word α).1) =
      cartanCasimirCoordinate α.1 := by
  simp only [cartanCasimirCoordinate]
  rw [cartanQuadratic_coordinateWordAction,
    cartanSextic_coordinateWordAction]

theorem coordinateWordAction_mem_cartanCasimirLevelSet
    (word : List Bool) (α : G2CoordinateRoot) :
    (coordinateWordAction word α).1 ∈ cartanCasimirLevelSet α.1 := by
  change cartanCasimirCoordinate ((coordinateWordAction word α).1) =
    cartanCasimirCoordinate α.1
  exact cartanCasimirCoordinate_coordinateWordAction word α

theorem coordinateWordAction_mem_cartanCasimirLevelSet_of_mem
    (word : List Bool) (v₀ : ℤ × ℤ) (α : G2CoordinateRoot)
    (hα : α.1 ∈ cartanCasimirLevelSet v₀) :
    (coordinateWordAction word α).1 ∈ cartanCasimirLevelSet v₀ := by
  change cartanCasimirCoordinate ((coordinateWordAction word α).1) =
    cartanCasimirCoordinate v₀
  rw [cartanCasimirCoordinate_coordinateWordAction word α]
  exact hα

end InfoGeometry.Algebra.Zorn.G2CartanCasimirCoordinates
