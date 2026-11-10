/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import Mathlib.Algebra.Lie.Basic
import Mathlib.Algebra.Lie.OfAssociative
import Mathlib.Tactic.NoncommRing
import InfoGeometry.Algebra.FiniteSpinAlgebra

namespace InfoGeometry.Algebra.TrialityG2

open InfoGeometry.Algebra.FiniteSpin

/-- Non-commutativity witness for the finite spin algebra carrier. -/
theorem exists_noncomm_pair :
    ∃ x y : Mat2C, x * y ≠ y * x :=
  ⟨J_plus, J_minus, j_plus_j_minus_ne⟩

section NonCommRingTriality

variable {B : Type*} [Ring B]

/-- Fixed point predicate for a ring endomorphism `σ : B →+* B` on `[Ring B]`. -/
def IsRingTrialityFixed (σ : B →+* B) (x : B) : Prop :=
  σ x = x

/-- Over any non-commutative ring `[Ring B]`, if `σ : B →+* B` is a ring endomorphism
and `σ x = ω * x`, `σ y = ω₂ * y` where `ω` commutes with `ω₂` and `y`, `ω₂` commutes
with `x`, and `ω * ω₂ = 1`, then the commutator `x * y - y * x` is fixed by `σ`. -/
theorem ring_commutator_fixed_of_inverse_eigen
    (σ : B →+* B) (ω ω₂ x y : B)
    (hx : σ x = ω * x) (hy : σ y = ω₂ * y)
    (hω : ω * ω₂ = 1) (hω₂ : ω₂ * ω = 1)
    (hω₂x : Commute ω₂ x) (hωy : Commute ω y) :
    IsRingTrialityFixed σ (x * y - y * x) := by
  dsimp [IsRingTrialityFixed]
  rw [map_sub, map_mul, map_mul, hx, hy]
  have h1 : (ω * x) * (ω₂ * y) = x * y := by
    calc
      (ω * x) * (ω₂ * y) = ω * (x * ω₂) * y := by noncomm_ring
      _ = ω * (ω₂ * x) * y := by rw [hω₂x.symm.eq]
      _ = (ω * ω₂) * (x * y) := by noncomm_ring
      _ = x * y := by rw [hω, one_mul]
  have h2 : (ω₂ * y) * (ω * x) = y * x := by
    calc
      (ω₂ * y) * (ω * x) = ω₂ * (y * ω) * x := by noncomm_ring
      _ = ω₂ * (ω * y) * x := by rw [hωy.symm.eq]
      _ = (ω₂ * ω) * (y * x) := by noncomm_ring
      _ = y * x := by rw [hω₂, one_mul]
  rw [h1, h2]

end NonCommRingTriality

/--
Triality automorphism data on a Lie algebra `L` over `K`.

This file records the order-three Lie equivalence and the associated fixed and
eigen carriers.  The full `D₄ → G₂` fixed-subalgebra theorem belongs to a
separate construction of the relevant Lie algebra and triality action.
-/
structure TrialityAutomorphism (K : Type*) [CommRing K]
    (L : Type*) [LieRing L] [LieAlgebra K L] where
  toEquiv : L ≃ₗ⁅K⁆ L
  order_three : ∀ x : L, toEquiv (toEquiv (toEquiv x)) = x

variable {K : Type*} [CommRing K] {L : Type*} [LieRing L] [LieAlgebra K L]

/-- The fixed carrier of a triality operator. -/
def fixedSet (σ : TrialityAutomorphism K L) : Set L :=
  {x | σ.toEquiv x = x}

/-- The `ω`-eigen carrier of a triality operator. -/
def trialityEigenspaceSet (ω : K) (σ : TrialityAutomorphism K L) : Set L :=
  {x | σ.toEquiv x = ω • x}

/--
Open theorem target for the cyclotomic bracket grading.

The proposition is exposed as a formal target for later proof transport.
-/
def eigenspaceBracketGradingStatement
    (σ : TrialityAutomorphism K L) (ω : K) : Prop :=
  ∀ x y : L,
    x ∈ trialityEigenspaceSet ω σ →
    y ∈ trialityEigenspaceSet (ω ^ 2) σ →
    ⁅x, y⁆ ∈ fixedSet σ

/-- Kernel proof of the cyclotomic bracket grading theorem: whenever `ω ^ 3 = 1`,
the Lie bracket of an `ω`-eigenvector and an `ω²`-eigenvector of `σ` lies in the
fixed subalgebra `fixedSet σ`. -/
theorem eigenspaceBracketGrading_of_cube_eq_one
    (σ : TrialityAutomorphism K L) (ω : K) (hω : ω ^ 3 = 1) :
    eigenspaceBracketGradingStatement σ ω := by
  intro x y hx hy
  change σ.toEquiv ⁅x, y⁆ = ⁅x, y⁆
  change σ.toEquiv x = ω • x at hx
  change σ.toEquiv y = (ω ^ 2) • y at hy
  have hpow : ω ^ 2 * ω = 1 := by
    calc
      ω ^ 2 * ω = ω ^ 2 * ω ^ 1 := by rw [pow_one]
      _ = ω ^ (2 + 1) := (pow_add ω 2 1).symm
      _ = 1 := hω
  rw [σ.toEquiv.map_lie, hx, hy, lie_smul, smul_lie, smul_smul, hpow, one_smul]

attribute [local instance 100] LieRing.ofAssociativeRing LieAlgebra.ofAssociativeAlgebra in
/-- Concrete ground inhabitant of `TrialityAutomorphism` over `ℤ`. -/
def intIdTrialityAutomorphism : TrialityAutomorphism ℤ ℤ where
  toEquiv := LieEquiv.refl
  order_three _ := rfl

end InfoGeometry.Algebra.TrialityG2
