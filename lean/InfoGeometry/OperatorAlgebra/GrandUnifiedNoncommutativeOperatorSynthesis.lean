/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import Mathlib.LinearAlgebra.Matrix.Notation
import Mathlib.Data.Matrix.Basic
import Mathlib.Algebra.Lie.OfAssociative
import Mathlib.Tactic
import Mathlib.Tactic.NoncommRing
import InfoGeometry.OperatorAlgebra.GerbeTwistedCurvatureTorsion
import InfoGeometry.Clifford.BrauerWeylMatrixStep

/-!
# Unified noncommutative operator identities

This file collects algebraic consequences in associative rings and genuine
operator matrix rings.  Differential, analytic, and characteristic-zero
hypotheses are retained where needed; no scalar or diagonal replacement is
used for the matrix constructions.
-/

open Matrix
attribute [local instance] LieRing.ofAssociativeRing

namespace InfoGeometry.OperatorAlgebra.GrandUnifiedNoncommutativeOperatorSynthesis

/-! ## The quadratic associative exponential jet -/

section Jet
variable {B : Type*} [Ring B]

def expJet2 (X : B) : B := 2 + 2 * X + X * X

theorem bch_jet2_commutator_obstruction (X Y : B) :
    expJet2 X * expJet2 Y - expJet2 Y * expJet2 X =
      4 * ⁅X, Y⁆ +
        2 * (X * X * Y - Y * (X * X) + X * (Y * Y) - Y * Y * X) +
        (X * X * (Y * Y) - Y * Y * (X * X)) := by
  dsimp [expJet2]
  rw [Ring.lie_def]
  noncomm_ring

theorem bch_jet2_nilpotent_commutator {X Y : B}
    (hX : X * X = 0) (hY : Y * Y = 0) :
    expJet2 X * expJet2 Y - expJet2 Y * expJet2 X = 4 * ⁅X, Y⁆ := by
  rw [bch_jet2_commutator_obstruction, hX, hY]
  noncomm_ring
end Jet

/-! ## Existing nested Clifford operator carrier

The matrix generators and their CAR/quaternion identities are owned by
`BrauerWeylMatrixStep`; this module names only the nested carriers used in its
master synthesis below.
-/

abbrev NestedMat (B : Type*) :=
  InfoGeometry.Clifford.BrauerWeylMatrixStep.NestedOp₂ B

def E₁ {B : Type*} [Ring B] : NestedMat B :=
  InfoGeometry.Clifford.BrauerWeylMatrixStep.outerRotation

def E₂ {B : Type*} [Ring B] : NestedMat B :=
  InfoGeometry.Clifford.BrauerWeylMatrixStep.outerKlein
    (InfoGeometry.Clifford.BrauerWeylMatrixStep.rotation :
      InfoGeometry.Clifford.BrauerWeylMatrixStep.Op₂ B)

def E₃ {B : Type*} [Ring B] : NestedMat B := (E₁ : NestedMat B) * E₂

/-! ## Derivation inverse rule -/

section Derivations
open InfoGeometry.OperatorAlgebra.GerbeTwistedCurvatureTorsion
variable {B : Type*} [Ring B]

/-- Differentiating `u * u⁻¹ = 1` and multiplying by `u⁻¹` on the left gives
the inverse rule in the same noncommutative ring as the connection calculus. -/
theorem IsRingDerivation.map_units_inv {d : B →+ B} (hd : IsRingDerivation d) (u : Bˣ) :
    d (↑u⁻¹ : B) = -(↑u⁻¹ : B) * d (u : B) * (↑u⁻¹ : B) := by
  have h1 := hd (u : B) (↑u⁻¹ : B)
  rw [Units.mul_inv, IsRingDerivation.map_one hd] at h1
  have hu : (↑u⁻¹ : B) * (u : B) = 1 := Units.inv_mul u
  have h2 := congrArg (fun z : B => (↑u⁻¹ : B) * z) h1
  have h3 : (↑u⁻¹ : B) * d (u : B) * (↑u⁻¹ : B) + d (↑u⁻¹ : B) = 0 := by
    simpa [mul_add, mul_assoc, hu] using h2.symm
  calc d (↑u⁻¹ : B)
      = ((↑u⁻¹ : B) * d (u : B) * (↑u⁻¹ : B) + d (↑u⁻¹ : B)) -
          (↑u⁻¹ : B) * d (u : B) * (↑u⁻¹ : B) := by abel
    _ = 0 - (↑u⁻¹ : B) * d (u : B) * (↑u⁻¹ : B) := by rw [h3]
    _ = -((↑u⁻¹ : B) * d (u : B) * (↑u⁻¹ : B)) := by simp
    _ = -(↑u⁻¹ : B) * d (u : B) * (↑u⁻¹ : B) := by noncomm_ring

end Derivations

/-! ## Derived uncovariantized Bianchi remainder

The covariant Bianchi identity and connection data are owned by
`GerbeTwistedCurvatureTorsion`.  This file records only the additional
algebraic consequence after expanding the adjoint covariant derivatives.
-/

section UncovariantizedBianchiRemainder
open InfoGeometry.OperatorAlgebra.GerbeTwistedCurvatureTorsion
variable {R : Type*} [Ring R]

theorem uncovariantized_bianchi_remainder {d₁ d₂ d₃ : R →+ R}
    (hd₁ : IsRingDerivation d₁) (hd₂ : IsRingDerivation d₂) (hd₃ : IsRingDerivation d₃)
    (h12 : ∀ x, d₁ (d₂ x) = d₂ (d₁ x))
    (h23 : ∀ x, d₂ (d₃ x) = d₃ (d₂ x))
    (h13 : ∀ x, d₁ (d₃ x) = d₃ (d₁ x)) (A₁ A₂ A₃ : R) :
    d₁ (curvature d₂ d₃ A₂ A₃) + d₂ (curvature d₃ d₁ A₃ A₁) +
      d₃ (curvature d₁ d₂ A₁ A₂) =
      ⁅curvature d₂ d₃ A₂ A₃, A₁⁆ + ⁅curvature d₃ d₁ A₃ A₁, A₂⁆ +
        ⁅curvature d₁ d₂ A₁ A₂, A₃⁆ := by
  let F₂₃ := curvature d₂ d₃ A₂ A₃
  let F₃₁ := curvature d₃ d₁ A₃ A₁
  let F₁₂ := curvature d₁ d₂ A₁ A₂
  have h := differentialBianchi hd₁ hd₂ hd₃ h12 h23 h13 A₁ A₂ A₃
  change (d₁ F₂₃ + ⁅A₁, F₂₃⁆) + (d₂ F₃₁ + ⁅A₂, F₃₁⁆) +
    (d₃ F₁₂ + ⁅A₃, F₁₂⁆) = 0 at h
  change d₁ F₂₃ + d₂ F₃₁ + d₃ F₁₂ = ⁅F₂₃, A₁⁆ + ⁅F₃₁, A₂⁆ + ⁅F₁₂, A₃⁆
  calc d₁ F₂₃ + d₂ F₃₁ + d₃ F₁₂
      = ((d₁ F₂₃ + ⁅A₁, F₂₃⁆) + (d₂ F₃₁ + ⁅A₂, F₃₁⁆) +
          (d₃ F₁₂ + ⁅A₃, F₁₂⁆)) +
        (⁅F₂₃, A₁⁆ + ⁅F₃₁, A₂⁆ + ⁅F₁₂, A₃⁆) := by
          simp only [Ring.lie_def]
          noncomm_ring
    _ = 0 + (⁅F₂₃, A₁⁆ + ⁅F₃₁, A₂⁆ + ⁅F₁₂, A₃⁆) := by rw [h]
    _ = ⁅F₂₃, A₁⁆ + ⁅F₃₁, A₂⁆ + ⁅F₁₂, A₃⁆ := by simp
end UncovariantizedBianchiRemainder

/-! ## Noncentral group braiding and its ordered cocycle -/

section GroupCocycle
variable {G : Type*} [Group G]

def conjugateBy (x q : G) : G := x * q * x⁻¹
def twistedCocycle (X Q : G) : ℕ → G
  | 0 => 1
  | n + 1 => Q * conjugateBy X (twistedCocycle X Q n)

theorem braided_pow_law {X Z Q : G} (h : Z * X = Q * X * Z) (n : ℕ) :
    Z * X ^ n = twistedCocycle X Q n * X ^ n * Z := by
  induction n with
  | zero => simp [twistedCocycle]
  | succ n ih =>
      calc Z * X ^ (n + 1)
          = (Z * X) * X ^ n := by rw [pow_succ']; group
        _ = (Q * X * Z) * X ^ n := by rw [h]
        _ = Q * X * (Z * X ^ n) := by group
        _ = Q * X * (twistedCocycle X Q n * X ^ n * Z) := by rw [ih]
        _ = twistedCocycle X Q (n + 1) * X ^ (n + 1) * Z := by
          rw [twistedCocycle, conjugateBy, pow_succ']
          group

theorem twistedCocycle_add (X Q : G) (m n : ℕ) :
    twistedCocycle X Q (m + n) =
      twistedCocycle X Q m * conjugateBy (X ^ m) (twistedCocycle X Q n) := by
  induction m with
  | zero => simp [twistedCocycle, conjugateBy]
  | succ m ih =>
      have hm : m + 1 + n = (m + n) + 1 := by omega
      rw [hm, twistedCocycle, ih, twistedCocycle]
      dsimp [conjugateBy]
      rw [pow_succ']
      group

theorem twistedCocycle_one_of_period {X Z Q : G}
    (h : Z * X = Q * X * Z) {N : ℕ} (hN : X ^ N = 1) :
    twistedCocycle X Q N = 1 := by
  have hp := braided_pow_law h N
  rw [hN, mul_one, mul_one] at hp
  calc twistedCocycle X Q N
      = (twistedCocycle X Q N * Z) * Z⁻¹ := by group
    _ = Z * Z⁻¹ := by rw [← hp]
    _ = 1 := by group
end GroupCocycle

/-! ## Clifford braid identity and operator commutator -/

section ArtinBraid
variable {B : Type*} [Ring B]

theorem clifford_bivector_triple_product {x y : B}
    (hx : x * x = -1) (hxy : x * y + y * x = 0) :
    (1 + x) * (1 + y) * (1 + x) = 2 * (x + y) := by
  have hx' : x * x + 1 = 0 := by rw [hx]; abel
  calc (1 + x) * (1 + y) * (1 + x)
      = 2 * (x + y) + (x * x + 1) * (1 - y) + (1 + x) * (x * y + y * x) := by noncomm_ring
    _ = 2 * (x + y) + 0 * (1 - y) + (1 + x) * 0 := by rw [hx', hxy]
    _ = 2 * (x + y) := by noncomm_ring

theorem clifford_artin_braid {x y : B}
    (hx : x * x = -1) (hy : y * y = -1) (hxy : x * y + y * x = 0) :
    (1 + x) * (1 + y) * (1 + x) = (1 + y) * (1 + x) * (1 + y) := by
  have hyx : y * x + x * y = 0 := by rw [add_comm, hxy]
  rw [clifford_bivector_triple_product hx hxy,
    clifford_bivector_triple_product hy hyx]
  noncomm_ring

def R12 : NestedMat B := 1 + E₁
def R23 : NestedMat B := 1 + E₂

open InfoGeometry.OperatorAlgebra.GerbeTwistedCurvatureTorsion

theorem quaternion_braid_and_commutator :
    (R12 : NestedMat B) * R23 * R12 = R23 * R12 * R23 ∧
    ⁅(R12 : NestedMat B), R23⁆ = (E₃ : NestedMat B) + E₃ := by
  have howner := InfoGeometry.Clifford.BrauerWeylMatrixStep.nested_quaternion_operator_relations
    (B := B)
  rcases howner with ⟨h₁, h₂, _, hcomm, _, _, _, _⟩
  have hanti : (E₁ : NestedMat B) * E₂ + E₂ * E₁ = 0 := by
    have h := InfoGeometry.Clifford.BrauerWeylMatrixStep.kleinTwist_anticomm_rotation
      (A := InfoGeometry.Clifford.BrauerWeylMatrixStep.Op₂ B)
      InfoGeometry.Clifford.BrauerWeylMatrixStep.rotation
    simpa [E₁, E₂, InfoGeometry.Clifford.BrauerWeylMatrixStep.outerRotation,
      InfoGeometry.Clifford.BrauerWeylMatrixStep.outerKlein, add_comm] using h
  have hcomm' : (E₁ : NestedMat B) * E₂ - E₂ * E₁ = E₃ + E₃ := by
    simpa [E₁, E₂, E₃, InfoGeometry.Clifford.BrauerWeylMatrixStep.outerRotation,
      InfoGeometry.Clifford.BrauerWeylMatrixStep.outerKlein, two_mul] using hcomm
  refine ⟨clifford_artin_braid h₁ h₂ hanti, ?_⟩
  · dsimp [R12, R23]
    rw [Ring.lie_def]
    calc (1 + E₁) * (1 + E₂) - (1 + E₂) * (1 + E₁)
        = E₁ * E₂ - E₂ * E₁ := by noncomm_ring
      _ = E₃ + E₃ := hcomm'

end ArtinBraid

end InfoGeometry.OperatorAlgebra.GrandUnifiedNoncommutativeOperatorSynthesis
