/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/

/- SPDX-License-Identifier: Apache-2.0 -/

import InfoGeometry.Algebra.Zorn.G2IntegralRootLattice
import Mathlib.Algebra.Module.LinearMap.Basic
import Mathlib.Tactic.Ring

/-!
# Integral linear Weyl action on the `G₂` root lattice

The coordinate reflections from `G2Roots` extend to `ℤ`-linear involutions on
the rank-two root lattice. The repository's finite Weyl owners separately
establish the order-12 group and its root action. This is a lattice
representation of the two generators; it does not identify the separate
24-sheet carrier with a cyclotomic operator representation.
-/

namespace InfoGeometry.Algebra.Zorn.G2IntegralWeylLatticeAction

open InfoGeometry.Algebra.Zorn.G2IntegralRootLattice
open InfoGeometry.Algebra.Zorn.G2Roots

def simpleReflectionOne : (ℤ × ℤ) →ₗ[ℤ] (ℤ × ℤ) where
  toFun := s1
  map_add' := by
    intro x y
    rcases x with ⟨a, b⟩
    rcases y with ⟨c, d⟩
    apply Prod.ext
    · simp [s1]
      ring
    · simp [s1]
  map_smul' := by
    intro r x
    rcases x with ⟨a, b⟩
    apply Prod.ext
    · simp [s1]
      ring
    · simp [s1]

def simpleReflectionTwo : (ℤ × ℤ) →ₗ[ℤ] (ℤ × ℤ) where
  toFun := s2
  map_add' := by
    intro x y
    rcases x with ⟨a, b⟩
    rcases y with ⟨c, d⟩
    apply Prod.ext
    · simp [s2]
    · simp [s2]
      ring
  map_smul' := by
    intro r x
    rcases x with ⟨a, b⟩
    apply Prod.ext
    · simp [s2]
    · simp [s2]
      ring

@[simp] theorem simpleReflectionOne_apply (v : ℤ × ℤ) :
    simpleReflectionOne v = s1 v := rfl

@[simp] theorem simpleReflectionTwo_apply (v : ℤ × ℤ) :
    simpleReflectionTwo v = s2 v := rfl

theorem simpleReflectionOne_square :
    simpleReflectionOne.comp simpleReflectionOne = LinearMap.id := by
  apply LinearMap.ext
  intro v
  exact s1_involutive v

theorem simpleReflectionTwo_square :
    simpleReflectionTwo.comp simpleReflectionTwo = LinearMap.id := by
  apply LinearMap.ext
  intro v
  exact s2_involutive v

/-- The root lattice is stable under each integral simple reflection. -/
theorem simpleReflections_preserve_integralRootLattice (v : ℤ × ℤ) :
    simpleReflectionOne v ∈ rootLattice ∧
    simpleReflectionTwo v ∈ rootLattice := by
  exact simpleReflections_preserve_rootLattice v

end InfoGeometry.Algebra.Zorn.G2IntegralWeylLatticeAction
