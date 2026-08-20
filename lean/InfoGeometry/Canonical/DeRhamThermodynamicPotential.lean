import Mathlib.Data.Real.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Tactic

import InfoGeometry.Canonical.PositiveRayCore
import InfoGeometry.Canonical.RelativePotentialCore

/-!
# De Rham Cohomology and Thermodynamic Exact Potentials

This module formalizes:
1. **Discrete de Rham complex on state space:**
   - 0-Forms (Scalar Potentials): `ZeroForm M := M → ℝ`
   - 1-Forms (Transition Forces / Scores): `OneForm M := M → M → ℝ`
   - Exterior derivative: `dZeroForm Φ x y = Φ y - Φ x`
2. **Stokes' Theorem / Exactness:**
   - Every exact 1-form `ω = dZeroForm Φ` satisfies path-independence (1-cocycle identity):
     `ω x z = ω x y + ω y z`
   - Reversibility / Zero loop integral:
     `ω y x = - ω x y` and `ω x x = 0`
3. **The Modular Potential as an Exact 1-Form:**
   - For any base state `q₀` and coordinate `a : α`, the 0-form `Φ(q) := V(q₀, q, a)`
     has exact exterior derivative `dZeroForm Φ q₁ q₂ = V(q₁, q₂, a)`.
   - The modular potential is strictly path-independent across intermediate states.

All proofs are complete in native Mathlib with zero `sorry`s.
-/

noncomputable section

namespace InfoGeometry.Canonical.DeRhamPotential

open InfoGeometry.Canonical.PositiveRayCore
open InfoGeometry.Canonical.RelativePotentialCore

variable {M : Type*}

/-- A scalar 0-form (potential function) on a state manifold M. -/
def ZeroForm (M : Type*) : Type _ := M → ℝ

/-- A transition 1-form (covector field / force) on state space M. -/
def OneForm (M : Type*) : Type _ := M → M → ℝ

/-- The discrete exterior derivative d₀ : Ω⁰(M) → Ω¹(M). -/
def dZeroForm (Φ : ZeroForm M) : OneForm M :=
  fun x y => Φ y - Φ x

@[simp]
theorem dZeroForm_apply (Φ : ZeroForm M) (x y : M) :
    dZeroForm Φ x y = Φ y - Φ x := rfl

/-- 
  THEOREM 1 (Exactness implies the 1-Cocycle Law):
  Every exact 1-form ω = d₀ Φ satisfies the additive transitive 1-cocycle identity:
    ω(x, z) = ω(x, y) + ω(y, z)
-/
theorem exact_oneForm_cocycle (Φ : ZeroForm M) (x y z : M) :
    dZeroForm Φ x z = dZeroForm Φ x y + dZeroForm Φ y z := by
  dsimp [dZeroForm]
  ring

/-- 
  THEOREM 2 (Reversibility / Skew-Symmetry of Exact 1-Forms):
  Reversing the transition direction flips the sign of the exact 1-form:
    ω(y, x) = - ω(x, y)
-/
theorem exact_oneForm_antisymm (Φ : ZeroForm M) (x y : M) :
    dZeroForm Φ y x = - dZeroForm Φ x y := by
  dsimp [dZeroForm]
  ring

/-- 
  THEOREM 3 (Closed Loop Vanishing / First Law of Thermodynamics):
  The line integral around any closed loop vanishes identically:
    ω(x, x) = 0
-/
theorem exact_oneForm_self (Φ : ZeroForm M) (x : M) :
    dZeroForm Φ x x = 0 := by
  dsimp [dZeroForm]
  ring

/-- Linearity of the exterior derivative d₀ on 0-forms. -/
theorem dZeroForm_linear (Φ Ψ : ZeroForm M) (c : ℝ) (x y : M) :
    dZeroForm (fun m => Φ m + c * Ψ m) x y = dZeroForm Φ x y + c * dZeroForm Ψ x y := by
  dsimp [dZeroForm]
  ring

/-!
=============================================================================
PART 2: The Relative Modular Potential as an Exact De Rham 1-Form
=============================================================================
-/

variable {α : Type*} [Fintype α] [Nonempty α]

/-- The modular potential 0-form based at reference state q₀. -/
def modularZeroForm (q₀ : PositiveRay α) (a : α) : ZeroForm (PositiveRay α) :=
  fun q => relativeModularPotential q₀ q a

/-- 
  THEOREM 4 (The Modular Potential IS That Exact Differential):
  The exterior derivative of the modular 0-form based at q₀ is identically
  the relative modular potential between any two states q₁ and q₂:
    d₀ (modularZeroForm q₀ a) q₁ q₂ = V(q₁, q₂, a)
-/
theorem relativeModularPotential_eq_dZeroForm (q₀ q₁ q₂ : PositiveRay α) (a : α) :
    dZeroForm (modularZeroForm q₀ a) q₁ q₂ = relativeModularPotential q₁ q₂ a := by
  dsimp [dZeroForm, modularZeroForm]
  have h := relativeModularPotential_cocycle q₀ q₁ q₂ a
  linarith

/-- 
  THEOREM 5 (Base-State Independence of the Exact Differential):
  The differential d₀ (modularZeroForm q₀ a) is independent of the choice of base state q₀.
-/
theorem modularZeroForm_deriv_independent (q₀ q₀' q₁ q₂ : PositiveRay α) (a : α) :
    dZeroForm (modularZeroForm q₀ a) q₁ q₂ = dZeroForm (modularZeroForm q₀' a) q₁ q₂ := by
  rw [relativeModularPotential_eq_dZeroForm, relativeModularPotential_eq_dZeroForm]

/-- 
  THEOREM 6 (Geometric Path-Independence of Modular Potential):
  The modular potential is strictly path-independent across intermediate states:
    V(q, q₂, a) = V(q, q₁, a) + V(q₁, q₂, a)
-/
theorem relativeModularPotential_path_independence (q q₁ q₂ : PositiveRay α) (a : α) :
    relativeModularPotential q q₂ a =
      relativeModularPotential q q₁ a + relativeModularPotential q₁ q₂ a :=
  relativeModularPotential_cocycle q q₁ q₂ a

end InfoGeometry.Canonical.DeRhamPotential

end noncomputable section
