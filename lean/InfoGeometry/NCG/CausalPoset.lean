/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/

import InfoGeometry.NCG.ZornCommutator
import InfoGeometry.NCG.PeirceGradingOperator
import InfoGeometry.NCG.TrialitySingletLieDerivation
import Mathlib.Tactic

/-!
# Causal order of noncommutative Zorn operator consequences

The dependency order is:

1. **Peirce Grading Operator** (`PeirceGradingOperator`): corner projectors P₊, P₋,
   grading involution η = P₊ − P₋, η² = 1, corner grading.
   η-conjugation is NOT a full algebra automorphism of OpZornMatrix A because
   the Zorn product is nonassociative. It is only an involution on the carrier.

2. **Zorn Commutator** (`ZornCommutator`): [X,Y] = X·Y − Y·X, antisymmetry,
   self-vanishing, Jacobiator = alternating sum of 6 associators,
   Jacobi identity on the associative x-axis sector `quatSubalgX`.

3. **Triality Singlet Sector** (`TrialitySingletLieDerivation`):
   singlet grade rays square-zero, associator = 0 on `zornSinglet`,
   Jacobi + Leibniz on singlets.

Composite results:
  C1. η acts on singlets by negating vector components:
      η·zornSinglet(a,c,d,b)·η = zornSinglet(a,-c,-d,b).
      singletGradePlusTwo and singletGradeMinusTwo are η-odd.
  C2. Opposite singlet grades contract to grade-0 Cartan nucleus:
      G₊₂(ξ)·G₋₂(η) = ⟨-ξ·η, 0, 0, 0⟩, G₋₂(η)·G₊₂(ξ) = ⟨0,0,0,-η·ξ⟩.
  C3. Jacobi on quatSubalgX; Jacobi + Leibniz on zornSinglet.

All results hold over any noncommutative ring [Ring A]; no scalar diagonal
or commuting-toy assumptions are used. -/

namespace InfoGeometry.NCG.CausalPoset

variable {A : Type*} [Ring A]

open InfoGeometry.Canonical.AlbertCayleyDickson
open InfoGeometry.Canonical.AlbertCayleyDickson.SplitQuaternion
open InfoGeometry.Canonical.AlbertCayleyDickson.SplitQuaternion.OpZornMatrix
open InfoGeometry.NCG.ZornCommutator
open InfoGeometry.NCG.PeirceGradingOperator
open InfoGeometry.NCG.TrialitySingletLieDerivation

/-- Level-2 composite: The Jacobiator vanishes on the x-axis sector.
  This is the associativity restoration that makes the commutator a Lie
  bracket on `quatSubalgX`. -/
theorem jacobi_on_xaxis
    (a₁ v₁ w₁ b₁ a₂ v₂ w₂ b₂ a₃ v₃ w₃ b₃ : A) :
    zornJacobiator (quatSubalgX a₁ v₁ w₁ b₁)
      (quatSubalgX a₂ v₂ w₂ b₂)
      (quatSubalgX a₃ v₃ w₃ b₃) = 0 := by
  exact zornJacobiator_vanishes_on_quatSubalgX
    a₁ v₁ w₁ b₁ a₂ v₂ w₂ b₂ a₃ v₃ w₃ b₃

/-- Level-3 composite: The triality-singlet sector has zero associator
  for arbitrary ordered coefficient products. -/
theorem singlet_associator_eq_zero
    (a₁ c₁ d₁ b₁ a₂ c₂ d₂ b₂ a₃ c₃ d₃ b₃ : A) :
    opAssociator (zornSinglet a₁ c₁ d₁ b₁)
      (zornSinglet a₂ c₂ d₂ b₂) (zornSinglet a₃ c₃ d₃ b₃) = 0 := by
  exact opAssociator_zornSinglet_eq_zero
    a₁ c₁ d₁ b₁ a₂ c₂ d₂ b₂ a₃ c₃ d₃ b₃

/-- Consequently, the commutator on the singlet sector satisfies Jacobi
  and the inner Leibniz identity. -/
theorem singlet_commutator_lie_identities
    (a₁ c₁ d₁ b₁ a₂ c₂ d₂ b₂ a₃ c₃ d₃ b₃ : A) :
    zornJacobiator (zornSinglet a₁ c₁ d₁ b₁)
      (zornSinglet a₂ c₂ d₂ b₂) (zornSinglet a₃ c₃ d₃ b₃) = 0 ∧
    opCommutator (zornSinglet a₁ c₁ d₁ b₁)
      ((zornSinglet a₂ c₂ d₂ b₂) * (zornSinglet a₃ c₃ d₃ b₃)) =
    opCommutator (zornSinglet a₁ c₁ d₁ b₁) (zornSinglet a₂ c₂ d₂ b₂) *
        zornSinglet a₃ c₃ d₃ b₃ +
    zornSinglet a₂ c₂ d₂ b₂ *
      opCommutator (zornSinglet a₁ c₁ d₁ b₁) (zornSinglet a₃ c₃ d₃ b₃) := by
  exact ⟨zornCommutator_jacobi_on_singlets
      a₁ c₁ d₁ b₁ a₂ c₂ d₂ b₂ a₃ c₃ d₃ b₃,
    zornCommutator_leibniz_on_singlets
      a₁ c₁ d₁ b₁ a₂ c₂ d₂ b₂ a₃ c₃ d₃ b₃⟩

/-- The same-grade singlet rays are square-zero even for noncommuting
coefficients. -/
theorem singlet_grade_rays_square_zero (ξ₁ ξ₂ η₁ η₂ : A) :
    singletGradePlusTwo ξ₁ * singletGradePlusTwo ξ₂ = 0 ∧
    singletGradeMinusTwo η₁ * singletGradeMinusTwo η₂ = 0 := by
  exact singlet_nilpotent_grading_closure ξ₁ ξ₂ η₁ η₂

/-- Opposite singlet grades contract in the exact coefficient order.
  The two orders occupy different diagonal entries. -/
theorem singlet_opposite_grade_products (ξ η : A) :
    singletGradePlusTwo ξ * singletGradeMinusTwo η =
      (⟨-OpVec3.dot (OpVec3.diagVec ξ) (OpVec3.diagVec η), 0, 0, 0⟩ :
        OpZornMatrix A) ∧
    singletGradeMinusTwo η * singletGradePlusTwo ξ =
      (⟨0, 0, 0, -OpVec3.dot (OpVec3.diagVec η) (OpVec3.diagVec ξ)⟩ :
        OpZornMatrix A) := by
  constructor <;> ext <;>
    simp [singletGradePlusTwo, singletGradeMinusTwo, OpVec3.diagVec,
      OpVec3.dot, OpVec3.skewCross,
      OpVec3.naiveCross, OpVec3.leftScale, OpVec3.rightScale]

/-- Level-1 composite: η acts on singlets by negating vector components.
  η·zornSinglet(a,c,d,b)·η = zornSinglet(a,-c,-d,b). The scalar parts (a,b)
  are η-even; the vector parts (c,d) are η-odd. -/
theorem eta_negates_singlet_vectors
    (a c d b : A) :
    eta_grading * zornSinglet a c d b * eta_grading =
      zornSinglet a (-c) (-d) b := by
  ext <;>
  simp [eta_grading, zornSinglet,
    mul_a, mul_b, mul_v, mul_w,
    OpVec3.diagVec, OpVec3.dot, OpVec3.skewCross, OpVec3.naiveCross,
    OpVec3.leftScale, OpVec3.rightScale] <;>
  (try noncomm_ring) <;>
  (try abel)

/-- singletGradePlusTwo is η-odd: η·G₊₂(c)·η = -G₊₂(c). -/
theorem eta_odd_grade_plus_two (c : A) :
    eta_grading * singletGradePlusTwo c * eta_grading =
      -singletGradePlusTwo c := by
  ext <;>
  simp [eta_grading, singletGradePlusTwo,
    mul_a, mul_b, mul_v, mul_w,
    OpVec3.diagVec, OpVec3.dot, OpVec3.skewCross, OpVec3.naiveCross,
    OpVec3.leftScale, OpVec3.rightScale] <;>
  (try noncomm_ring) <;>
  (try abel)

/-- singletGradeMinusTwo is η-odd: η·G₋₂(d)·η = -G₋₂(d). -/
theorem eta_odd_grade_minus_two (d : A) :
    eta_grading * singletGradeMinusTwo d * eta_grading =
      -singletGradeMinusTwo d := by
  ext <;>
  simp [eta_grading, singletGradeMinusTwo,
    mul_a, mul_b, mul_v, mul_w,
    OpVec3.diagVec, OpVec3.dot, OpVec3.skewCross, OpVec3.naiveCross,
    OpVec3.leftScale, OpVec3.rightScale] <;>
  (try noncomm_ring) <;>
  (try abel)

end InfoGeometry.NCG.CausalPoset
