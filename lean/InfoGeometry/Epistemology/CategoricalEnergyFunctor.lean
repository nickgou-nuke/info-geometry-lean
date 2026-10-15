/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import Mathlib.CategoryTheory.Category.Basic
import Mathlib.CategoryTheory.Preadditive.Basic
import Mathlib.Order.Hom.Basic
import InfoGeometry.Epistemology.JungianEpistemicCompiler
import InfoGeometry.Physics.ChevalleyDyads

/-!
# Categorical Energy Stationarity & Continuous-to-Discrete Poset Embedding

This module formalizes the algebraic projection shadow of continuous energy-minimization
dynamics and discrete Curry–Howard poset embedding in an ambient preadditive category `C`.

It establishes:
1. Abstract gradient kernels and complementary stationary defect operators.
2. The regular element (von Neumann regular) split idempotent resolving the stationary subspace.
3. Order-preserving monotone embedding from energy certification levels into the discrete epistemic poset
   `UnconsciousArchetype`.
4. Exact identification of the stationary projector with Chevalley dyadic vacuum projectors.
-/

namespace InfoGeometry.Epistemology.EnergyFunctor

open CategoryTheory
open InfoGeometry.Physics.ChevalleyDyads
open InfoGeometry.Epistemology.JungianEpistemicCompiler

universe v u

variable {C : Type u} [Category.{v} C] [Preadditive C]

/-! ### 1. Abstract Energy Potentials and Stationary Defect -/

/-- Definitional convenience wrapper identifying a designated endomorphism as an
abstract gradient operator `G : X ⟶ X`. Stationary states correspond to `u ≫ G = 0`. -/
@[inline]
def energyGradient {X : C} (G : X ⟶ X) : X ⟶ X :=
  G

/-- A state `u : S ⟶ X` is stationary with respect to gradient `G` if it lies in the kernel: `u ≫ G = 0`. -/
def IsStationaryState {S X : C} (u : S ⟶ X) (G : X ⟶ X) : Prop :=
  u ≫ G = 0

/-- The stationary defect operator `D = 𝟙 X - P` relative to an idempotent projector `P`. -/
@[inline]
def stationaryDefect {X : C} (P : X ⟶ X) : X ⟶ X :=
  𝟙 X - P

/-- Idempotency of the stationary projector implies annihilation of the defect:
`P ≫ (𝟙 X - P) = 0`. -/
theorem stationary_projector_annihilates_defect {X : C} (P : X ⟶ X)
    (hP_idem : P ≫ P = P) :
    P ≫ stationaryDefect P = 0 := by
  dsimp [stationaryDefect]
  rw [Preadditive.comp_sub, Category.comp_id, hP_idem, sub_self]

/-! ### 2. Regular Projectors and Duality-Invariant Subspaces -/

omit [Preadditive C] in
/-- A generalized regular pair `(F, F_star)` satisfying the von Neumann 3-cycle
condition `F ≫ F_star ≫ F = F` yields an idempotent projector `P = F ≫ F_star`. -/
theorem regular_projector_idempotent {X : C} (F F_star : X ⟶ X)
    (h_cycle : F ≫ F_star ≫ F = F) :
    (F ≫ F_star) ≫ (F ≫ F_star) = F ≫ F_star := by
  calc (F ≫ F_star) ≫ (F ≫ F_star)
    _ = (F ≫ F_star ≫ F) ≫ F_star := by simp only [Category.assoc]
    _ = F ≫ F_star                 := by rw [h_cycle]

omit [Preadditive C] in
/-- Backward-compatible alias for `regular_projector_idempotent`. -/
theorem bregman_duality_projector_idempotent {X : C} (F F_star : X ⟶ X)
    (h_cycle : F ≫ F_star ≫ F = F) :
    (F ≫ F_star) ≫ (F ≫ F_star) = F ≫ F_star :=
  regular_projector_idempotent F F_star h_cycle

/-- The stationary certificate projector `P_cert = F ≫ F_star` isolates states
invariant under the regular cycle. -/
@[inline]
def certificationProjector {X : C} (F F_star : X ⟶ X) : X ⟶ X :=
  F ≫ F_star

omit [Preadditive C] in
/-- Convenience theorem verifying that certified states invariant under `F ≫ F_star`
are identically fixed by `certificationProjector F F_star`. -/
theorem certified_state_invariant {S X : C} (u : S ⟶ X) (F F_star : X ⟶ X)
    (h_cert : u ≫ (F ≫ F_star) = u) :
    u ≫ certificationProjector F F_star = u :=
  h_cert

/-! ### 3. Discretization: Order-Theoretic Poset Embedding -/

/-- State classification into epistemic stages based on energy certification.
A state is mapped to `.primaMateria` if uncertified, and to `.selfIndividuation`
if fully certified by the regular projector. -/
inductive EpistemicCertificationLevel where
  | uncertified : EpistemicCertificationLevel
  | certified   : EpistemicCertificationLevel
  deriving DecidableEq, Repr

instance : LE EpistemicCertificationLevel where
  le a b := match a, b with
    | .uncertified, _ => True
    | .certified, .certified => True
    | .certified, .uncertified => False

instance : DecidableRel ((· ≤ ·) : EpistemicCertificationLevel → EpistemicCertificationLevel → Prop) :=
  fun a b => by
    cases a <;> cases b <;> dsimp [(· ≤ ·), LE.le] <;> infer_instance

instance : PartialOrder EpistemicCertificationLevel where
  le_refl a := by cases a <;> trivial
  le_trans a b c := by cases a <;> cases b <;> cases c <;> intro _ _ <;> trivial
  le_antisymm := fun a b => by
    cases a <;> cases b
    · intro _ _; rfl
    · intro _ h; contradiction
    · intro h _; contradiction
    · intro _ _; rfl

/-- Canonical embedding of continuous certification levels into the discrete
causal archetype poset. -/
def toCausalArchetype : EpistemicCertificationLevel → UnconsciousArchetype
  | .uncertified => .primaMateria
  | .certified   => .selfIndividuation

/-- Monotonicity of the certification map: Higher certification preserves causal poset order. -/
theorem certification_respects_causal_order (lvl1 lvl2 : EpistemicCertificationLevel)
    (h_le : lvl1 ≤ lvl2) :
    toCausalArchetype lvl1 ≤ toCausalArchetype lvl2 := by
  cases lvl1 <;> cases lvl2
  · dsimp [toCausalArchetype]; rfl
  · dsimp [toCausalArchetype]; decide
  · contradiction
  · dsimp [toCausalArchetype]; rfl

/-- The canonical order-preserving homomorphism from certification levels into archetypes. -/
def toCausalArchetypeOrderHom : EpistemicCertificationLevel →o UnconsciousArchetype where
  toFun := toCausalArchetype
  monotone' := fun _ _ => certification_respects_causal_order _ _

/-! ### 4. Linking Continuous Energy Minima to Chevalley Dyadic Projectors -/

/-- When the state space is polarized by isotropic nilpotents `(n, p)`, the stationary
certification projector coincides with the vacuum dyadic projector `E00 = n ≫ p`. -/
theorem dyadic_energy_minima_is_vacuum_projector {X : C} (n p : X ⟶ X)
    (hn : n ≫ n = 0) (hcar : n ≫ p + p ≫ n = 𝟙 X) :
    certificationProjector n p = E00 n p := by
  dsimp [certificationProjector]
  exact (E00_eq_np n p hn hcar).symm

/-- The zero-energy vacuum state `e0` has zero stationary defect:
`e0 ≫ (𝟙 X - E00) = 0`. -/
theorem vacuum_state_zero_defect {X : C} (n p : X ⟶ X)
    (hn : n ≫ n = 0) (hcar : n ≫ p + p ≫ n = 𝟙 X) :
    e0 n p ≫ stationaryDefect (E00 n p) = 0 := by
  have hE00 : E00 n p = e0 n p := E00_eq_np n p hn hcar
  rw [hE00]
  dsimp [stationaryDefect]
  rw [Preadditive.comp_sub, Category.comp_id]
  rw [e0_idempotent n p hn hcar, sub_self]

end InfoGeometry.Epistemology.EnergyFunctor
