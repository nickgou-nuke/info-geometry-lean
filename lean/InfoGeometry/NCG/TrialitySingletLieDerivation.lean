/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/

import InfoGeometry.NCG.ZornCommutator
import Mathlib.Tactic

/-!
# Triality-fixed noncommutative Zorn sector

The coefficient ring is arbitrary and may be noncommutative.  The carrier is
the actual `OpZornMatrix A` of the Albert–Cayley–Dickson owner.  This file
records the causal chain: triality-singlet grade rays are square-zero, then
the ambient commutator obeys Jacobi and the inner Leibniz identity when all
arguments lie in the associative triality-fixed sector.

The axis-fixed results live separately in `AxisFixedSectorLieDerivation`;
these singlet statements concern the distinct `zornSinglet` carrier.
-/

namespace InfoGeometry.NCG.TrialitySingletLieDerivation

variable {A : Type*} [Ring A]

open InfoGeometry.Canonical.AlbertCayleyDickson
open InfoGeometry.Canonical.AlbertCayleyDickson.SplitQuaternion
open InfoGeometry.Canonical.AlbertCayleyDickson.SplitQuaternion.OpZornMatrix
open InfoGeometry.NCG.ZornCommutator

/-- Grade `+2` ray in the triality-fixed sector: all three vector coordinates
are the same coefficient. -/
def singletGradePlusTwo (ξ : A) : OpZornMatrix A :=
  ⟨0, OpVec3.diagVec ξ, 0, 0⟩

/-- Grade `-2` ray in the triality-fixed sector. -/
def singletGradeMinusTwo (η : A) : OpZornMatrix A :=
  ⟨0, 0, OpVec3.diagVec η, 0⟩

/-- Both same-grade products vanish, with no commutativity assumption on the
coefficients: each cross-product component is the identical ordered product
subtracted from itself. -/
theorem singlet_nilpotent_grading_closure (ξ₁ ξ₂ η₁ η₂ : A) :
    singletGradePlusTwo ξ₁ * singletGradePlusTwo ξ₂ = 0 ∧
    singletGradeMinusTwo η₁ * singletGradeMinusTwo η₂ = 0 := by
  constructor <;>
    ext <;>
    simp [singletGradePlusTwo, singletGradeMinusTwo, OpVec3.diagVec,
      mul_a, mul_b, mul_v, mul_w, OpVec3.dot, OpVec3.skewCross,
      OpVec3.naiveCross, OpVec3.leftScale, OpVec3.rightScale]

/-- The triality-fixed singlet carrier is associative for arbitrary,
possibly noncommuting coefficients. The factor `3` in the scalar-vector
contractions occurs in both parenthesizations. -/
theorem opAssociator_zornSinglet_eq_zero
    (a₁ c₁ d₁ b₁ a₂ c₂ d₂ b₂ a₃ c₃ d₃ b₃ : A) :
    opAssociator (zornSinglet a₁ c₁ d₁ b₁)
      (zornSinglet a₂ c₂ d₂ b₂) (zornSinglet a₃ c₃ d₃ b₃) = 0 := by
  ext <;>
    simp [opAssociator, zornSinglet,
      OpVec3.diagVec, mul_a, mul_b, mul_v, mul_w,
      OpVec3.dot, OpVec3.skewCross, OpVec3.naiveCross,
      OpVec3.leftScale, OpVec3.rightScale] <;>
    noncomm_ring

/-- The commutator Jacobi identity on the triality-fixed singlet subalgebra.
This is a restriction to the owner-proved associative sector; it is not a
Jacobi claim for the full nonassociative Zorn carrier. -/
theorem zornCommutator_jacobi_on_singlets
    (a₁ c₁ d₁ b₁ a₂ c₂ d₂ b₂ a₃ c₃ d₃ b₃ : A) :
    zornJacobiator (zornSinglet a₁ c₁ d₁ b₁)
      (zornSinglet a₂ c₂ d₂ b₂) (zornSinglet a₃ c₃ d₃ b₃) = 0 := by
  rw [zornJacobiator_eq_alternating_associator]
  simp [opAssociator_zornSinglet_eq_zero]

/-- An inner commutator acts as a product derivation on the triality-fixed
singlet sector. -/
theorem zornCommutator_leibniz_on_singlets
    (a₁ c₁ d₁ b₁ a₂ c₂ d₂ b₂ a₃ c₃ d₃ b₃ : A) :
    opCommutator (zornSinglet a₁ c₁ d₁ b₁)
      ((zornSinglet a₂ c₂ d₂ b₂) * (zornSinglet a₃ c₃ d₃ b₃)) =
    opCommutator (zornSinglet a₁ c₁ d₁ b₁)
        (zornSinglet a₂ c₂ d₂ b₂) * zornSinglet a₃ c₃ d₃ b₃ +
    zornSinglet a₂ c₂ d₂ b₂ *
      opCommutator (zornSinglet a₁ c₁ d₁ b₁)
        (zornSinglet a₃ c₃ d₃ b₃) := by
  have h := opCommutator_leibniz_defect_eq_associators
    (zornSinglet a₁ c₁ d₁ b₁) (zornSinglet a₂ c₂ d₂ b₂)
    (zornSinglet a₃ c₃ d₃ b₃)
  simp [opAssociator_zornSinglet_eq_zero] at h
  exact sub_eq_zero.mp h

end InfoGeometry.NCG.TrialitySingletLieDerivation
