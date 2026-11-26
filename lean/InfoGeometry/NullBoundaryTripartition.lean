/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/

import InfoGeometry.Core.PeirceDecomposition
import InfoGeometry.Physics.Algebra.TripotentPeirceProjectors
import InfoGeometry.Physics.Order27DeHaroModelBundleSheaf
import InfoGeometry.Clifford.GEMMidpointRotorBogoliubovQGT
import InfoGeometry.Canonical.Cl55InfinityWittBoundary
import InfoGeometry.Canonical.CantorSplitNullBridge
import InfoGeometry.Canonical.ConcreteHilbertSewnAnomaly
import InfoGeometry.OperatorAlgebra.PeirceBiSandwich.CustodialTwinLoopAndJosephsonLattice
import InfoGeometry.Lie.Pin55NondegenerateKreinBridge
import InfoGeometry.Lie.SO55GlobalConformalPrecursors
import InfoGeometry.Algebra.WeylCartanKANPolarEquivariance
import InfoGeometry.Algebra.NoncommutativeWeylCartanKANPolarEquivariance
import InfoGeometry.Parafermion.ParafermionBraidBrownGaussPoset
import Mathlib.Analysis.InnerProductSpace.l2Space

/-!
# Null Boundary Tripartition Synthesis: Carriers, Intertwiners & Soldering

Unifies the complete algebraic stack for the topological boundary as the null space
`P₀` out of the Peirce tripartition `P₁ + P₀ + P₂ = 1` arising from a tripotent `T³ = T`.

## CARRIERS (The Seven Layers)

| Layer | Carrier | Key Map | Soldering / Intertwiner |
|-------|---------|---------|------------------------|
| **0. Abstract Tripotent** | `TripotentTripartition T` | `T ↦ (P₁, P₀, P₂)` | `T·P₁=P₁, T·P₂=-P₂, T·P₀=0` |
| **1. Nilpotent Boundary** | `NilpotentBoundaryOperators` | `N₁₀=P₁XP₀, N₀₂=P₀YP₂` | `[N₁₀,N₀₂]=N₁₂=P₁XP₀YP₂` |
| **2. Chiral Lightcone** | `GEMInP0` (in `Mat16Prod`) | `F = P₀EP₀ + P₀IP₀ · P₀BP₀` | `γ₀Fγ₀ = -P₀EP₀ + P₀IP₀ · P₀BP₀` |
| **3. Circular Polarized** | `parafermionFromPeirceBits` | `Z₄` generator | `ζ⁴=-1` from `real_eighth_root_carry_and_inverse` |
| **4. Witt 4-Vectors** | `Cl55InfinityWittBoundary` | `∞=½n̄, 0=½n` | `CAR: ι(∞)ι(0)+ι(0)ι(∞)=1` |
| **5. Sewn Hilbert** | `H_lp E = ℓ²(Cantor, E×E)` | `J_lp, ε_lp` | `Cl(1,1): J²=1, ε²=1, Jε=-εJ=K` |
| **6. Modular Flow** | `so55Boost on NullQuadric` | `Λ(ξ)` | `KMS β=1, Spohn entropy ≥ 0` |
-/

noncomputable section

open InfoGeometry.Core.PeirceDecomposition
open InfoGeometry.Physics.Algebra
open InfoGeometry.Physics.Order27DeHaroModelBundleSheaf
open InfoGeometry.Clifford.GEMMidpointRotorBogoliubovQGT
open InfoGeometry.Clifford.Clifford55
open ProjectiveAffineConformalClosure55
open InfoGeometry.Canonical.Cl55InfinityWittBoundary
open InfoGeometry.Canonical.CantorSplitNullBridge
open InfoGeometry.Canonical.ConcreteHilbertCommutation
open InfoGeometry.Canonical.ConcreteHilbertSewnAnomaly
open InfoGeometry.OperatorAlgebra.PeirceBiSandwich
open InfoGeometry.Lie.Pin55NondegenerateKreinBridge
open InfoGeometry.Lie.SO55GlobalConformalPrecursors
open InfoGeometry.Algebra.WeylCartanKANPolarEquivariance
open InfoGeometry.Algebra.NoncommutativeWeylCartanKANPolarEquivariance
open InfoGeometry.Parafermion.ParafermionBraidBrownGaussPoset

open scoped Kronecker

namespace InfoGeometry.NullBoundaryTripartition

/-! ===========================================================================
LAYER 0: Abstract Tripotent Tripartition (T³ = T)
=========================================================================== -/

section TripotentLayer

variable {R : Type*} [Ring R] [Algebra ℝ R]

/-- A tripotent element `T` with `T³ = T` and its three polynomial projectors. -/
structure TripotentTripartition (T : R) where
  hT : T * T * T = T
  P1 : R := projPos T
  P0 : R := projZero T
  P2 : R := projNeg T
  hP1 : P1 = projPos T
  hP0 : P0 = projZero T
  hP2 : P2 = projNeg T

/-- Construct the canonical tripotent tripartition from a tripotent element. -/
def canonicalTripotentTripartition (T : R) (hT : T * T * T = T) : TripotentTripartition T :=
  { hT := hT, hP1 := rfl, hP0 := rfl, hP2 := rfl }

/-- The three projectors sum to identity: `P₁ + P₀ + P₂ = 1`. -/
theorem tripotent_sum_eq_one {T : R} (tri : TripotentTripartition T) :
    tri.P1 + tri.P0 + tri.P2 = 1 := by
  rw [tri.hP1, tri.hP0, tri.hP2, projPos, projZero, projNeg]
  have h12 : (1 / 2 : ℝ) • (T * T + T) + (1 / 2 : ℝ) • (T * T - T) = T * T := by
    rw [← smul_add]
    have hsum : (T * T + T) + (T * T - T) = (2 : ℝ) • (T * T) := by
      rw [two_smul]
      abel
    rw [hsum, smul_smul]
    norm_num
  calc
    (1 / 2 : ℝ) • (T * T + T) + (1 - T * T) + (1 / 2 : ℝ) • (T * T - T)
      = ((1 / 2 : ℝ) • (T * T + T) + (1 / 2 : ℝ) • (T * T - T)) + (1 - T * T) := by abel
    _ = T * T + (1 - T * T) := by rw [h12]
    _ = 1 := by abel

omit [Algebra ℝ R] in
private lemma tripotent_four {T : R} (hT : T * T * T = T) : T * T * T * T = T * T := by
  calc
    T * T * T * T = (T * T * T) * T := rfl
    _ = T * T := by rw [hT]

/-- The three projectors are pairwise orthogonal: `Pᵢ Pⱼ = 0` for `i ≠ j`. -/
theorem tripotent_orthogonal {T : R} (tri : TripotentTripartition T) :
    tri.P1 * tri.P0 = 0 ∧ tri.P0 * tri.P1 = 0 ∧
    tri.P1 * tri.P2 = 0 ∧ tri.P2 * tri.P1 = 0 ∧
    tri.P0 * tri.P2 = 0 ∧ tri.P2 * tri.P0 = 0 := by
  have hT4 : T * T * T * T = T * T := tripotent_four tri.hT
  have hT3 : T * T * T = T := tri.hT
  rw [tri.hP1, tri.hP0, tri.hP2, projPos, projZero, projNeg]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [Algebra.smul_mul_assoc]
    have h : (T * T + T) * (1 - T * T) = 0 := by
      calc
        (T * T + T) * (1 - T * T) = (T * T + T) - ((T * T * T * T) + (T * T * T)) := by
          noncomm_ring
        _ = (T * T + T) - (T * T + T) := by rw [hT4, hT3]
        _ = 0 := sub_self _
    rw [h, smul_zero]
  · rw [Algebra.mul_smul_comm]
    have h : (1 - T * T) * (T * T + T) = 0 := by
      calc
        (1 - T * T) * (T * T + T) = (T * T + T) - ((T * T * T * T) + (T * T * T)) := by
          noncomm_ring
        _ = (T * T + T) - (T * T + T) := by rw [hT4, hT3]
        _ = 0 := sub_self _
    rw [h, smul_zero]
  · rw [Algebra.smul_mul_assoc, Algebra.mul_smul_comm, smul_smul]
    have h : (T * T + T) * (T * T - T) = 0 := by
      calc
        (T * T + T) * (T * T - T) = T * T * T * T - T * T := by noncomm_ring
        _ = T * T - T * T := by rw [hT4]
        _ = 0 := sub_self _
    rw [h, smul_zero]
  · rw [Algebra.smul_mul_assoc, Algebra.mul_smul_comm, smul_smul]
    have h : (T * T - T) * (T * T + T) = 0 := by
      calc
        (T * T - T) * (T * T + T) = T * T * T * T - T * T := by noncomm_ring
        _ = T * T - T * T := by rw [hT4]
        _ = 0 := sub_self _
    rw [h, smul_zero]
  · rw [Algebra.mul_smul_comm]
    have h : (1 - T * T) * (T * T - T) = 0 := by
      calc
        (1 - T * T) * (T * T - T) = (T * T - T) - (T * T * T * T - T * T * T) := by
          noncomm_ring
        _ = (T * T - T) - (T * T - T) := by rw [hT4, hT3]
        _ = 0 := sub_self _
    rw [h, smul_zero]
  · rw [Algebra.smul_mul_assoc]
    have h : (T * T - T) * (1 - T * T) = 0 := by
      calc
        (T * T - T) * (1 - T * T) = (T * T - T) - (T * T * T * T - T * T * T) := by
          noncomm_ring
        _ = (T * T - T) - (T * T - T) := by rw [hT4, hT3]
        _ = 0 := sub_self _
    rw [h, smul_zero]

/-- Each projector is idempotent: `Pᵢ² = Pᵢ`. -/
theorem tripotent_idempotent {T : R} (tri : TripotentTripartition T) :
    tri.P1 * tri.P1 = tri.P1 ∧ tri.P0 * tri.P0 = tri.P0 ∧ tri.P2 * tri.P2 = tri.P2 := by
  have hT4 : T * T * T * T = T * T := tripotent_four tri.hT
  have hT3 : T * T * T = T := tri.hT
  rw [tri.hP1, tri.hP0, tri.hP2, projPos, projZero, projNeg]
  refine ⟨?_, ?_, ?_⟩
  · rw [Algebra.smul_mul_assoc, Algebra.mul_smul_comm, smul_smul]
    have h : (T * T + T) * (T * T + T) = (2 : ℝ) • (T * T + T) := by
      calc
        (T * T + T) * (T * T + T) = T * T * T * T + T * T * T + T * T * T + T * T := by
          noncomm_ring
        _ = T * T + T + T + T * T := by rw [hT4, hT3]
        _ = (T * T + T) + (T * T + T) := by abel
        _ = (2 : ℝ) • (T * T + T) := (two_smul ℝ _).symm
    rw [h, smul_smul]
    norm_num
  · calc
      (1 - T * T) * (1 - T * T) = 1 - T * T - T * T + T * T * T * T := by noncomm_ring
      _ = 1 - T * T - T * T + T * T := by rw [hT4]
      _ = 1 - T * T := by abel
  · rw [Algebra.smul_mul_assoc, Algebra.mul_smul_comm, smul_smul]
    have h : (T * T - T) * (T * T - T) = (2 : ℝ) • (T * T - T) := by
      calc
        (T * T - T) * (T * T - T) = T * T * T * T - T * T * T - T * T * T + T * T := by
          noncomm_ring
        _ = T * T - T - T + T * T := by rw [hT4, hT3]
        _ = (T * T - T) + (T * T - T) := by abel
        _ = (2 : ℝ) • (T * T - T) := (two_smul ℝ _).symm
    rw [h, smul_smul]
    norm_num

/-- The tripotent element `T` acts on the projectors: `T·P₁ = P₁`, `T·P₂ = -P₂`, `T·P₀ = 0`. -/
theorem tripotent_action {T : R} (tri : TripotentTripartition T) :
    T * tri.P1 = tri.P1 ∧ tri.P1 * T = tri.P1 ∧
    T * tri.P2 = -tri.P2 ∧ tri.P2 * T = -tri.P2 ∧
    T * tri.P0 = 0 ∧ tri.P0 * T = 0 := by
  have hT3 : T * T * T = T := tri.hT
  have hTT_comm : T * (T * T) = T * T * T := (mul_assoc T T T).symm
  rw [tri.hP1, tri.hP0, tri.hP2, projPos, projZero, projNeg]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [Algebra.mul_smul_comm]
    congr 1
    calc
      T * (T * T + T) = T * (T * T) + T * T := mul_add _ _ _
      _ = T * T * T + T * T := by rw [hTT_comm]
      _ = T + T * T := by rw [hT3]
      _ = T * T + T := add_comm _ _
  · rw [Algebra.smul_mul_assoc]
    congr 1
    calc
      (T * T + T) * T = T * T * T + T * T := add_mul _ _ _
      _ = T + T * T := by rw [hT3]
      _ = T * T + T := add_comm _ _
  · rw [Algebra.mul_smul_comm, ← smul_neg]
    congr 1
    calc
      T * (T * T - T) = T * (T * T) - T * T := mul_sub _ _ _
      _ = T * T * T - T * T := by rw [hTT_comm]
      _ = T - T * T := by rw [hT3]
      _ = -(T * T - T) := by abel
  · rw [Algebra.smul_mul_assoc, ← smul_neg]
    congr 1
    calc
      (T * T - T) * T = T * T * T - T * T := sub_mul _ _ _
      _ = T - T * T := by rw [hT3]
      _ = -(T * T - T) := by abel
  · calc
      T * (1 - T * T) = T - T * (T * T) := by rw [mul_sub, mul_one]
      _ = T - T * T * T := by rw [hTT_comm]
      _ = T - T := by rw [hT3]
      _ = 0 := sub_self _
  · calc
      (1 - T * T) * T = T - (T * T) * T := by rw [sub_mul, one_mul]
      _ = T - T := by rw [hT3]
      _ = 0 := sub_self _

/-! ===========================================================================
LAYER 1: Nilpotent Boundary Operators
=========================================================================== -/

/-- The nilpotent boundary operators generated from the tripartition. -/
structure NilpotentBoundaryOperators (T : R) where
  X : R
  Y : R
  tri : TripotentTripartition T
  N10 : R := tri.P1 * X * tri.P0
  N02 : R := tri.P0 * Y * tri.P2
  N12 : R := tri.P1 * X * tri.P0 * Y * tri.P2
  hN10 : N10 = tri.P1 * X * tri.P0
  hN02 : N02 = tri.P0 * Y * tri.P2
  hN12 : N12 = tri.P1 * X * tri.P0 * Y * tri.P2

/-- Construct nilpotent boundary operators from a tripotent. -/
def canonicalNilpotentBoundaryOperators {T : R} (hT : T * T * T = T) (X Y : R) :
    NilpotentBoundaryOperators T :=
  { X := X
    Y := Y
    tri := canonicalTripotentTripartition T hT
    hN10 := rfl
    hN02 := rfl
    hN12 := rfl }

/-- `N₁₀ = P₁ X P₀` is square-zero nilpotent: `N₁₀² = 0`. -/
theorem N10_square_zero {T : R} (ops : NilpotentBoundaryOperators T) :
    ops.N10 * ops.N10 = 0 := by
  rw [ops.hN10]
  have hP0P1 : ops.tri.P0 * ops.tri.P1 = 0 := (tripotent_orthogonal ops.tri).2.1
  calc
    (ops.tri.P1 * ops.X * ops.tri.P0) * (ops.tri.P1 * ops.X * ops.tri.P0)
      = ops.tri.P1 * ops.X * (ops.tri.P0 * ops.tri.P1) * ops.X * ops.tri.P0 := by noncomm_ring
    _ = ops.tri.P1 * ops.X * 0 * ops.X * ops.tri.P0 := by rw [hP0P1]
    _ = 0 := by noncomm_ring

/-- `N₀₂ = P₀ Y P₂` is square-zero nilpotent: `N₀₂² = 0`. -/
theorem N02_square_zero {T : R} (ops : NilpotentBoundaryOperators T) :
    ops.N02 * ops.N02 = 0 := by
  rw [ops.hN02]
  have hP2P0 : ops.tri.P2 * ops.tri.P0 = 0 := (tripotent_orthogonal ops.tri).2.2.2.2.2
  calc
    (ops.tri.P0 * ops.Y * ops.tri.P2) * (ops.tri.P0 * ops.Y * ops.tri.P2)
      = ops.tri.P0 * ops.Y * (ops.tri.P2 * ops.tri.P0) * ops.Y * ops.tri.P2 := by noncomm_ring
    _ = ops.tri.P0 * ops.Y * 0 * ops.Y * ops.tri.P2 := by rw [hP2P0]
    _ = 0 := by noncomm_ring

/-- `N₁₂ = [N₁₀, N₀₂] = N₁₀ N₀₂ - N₀₂ N₁₀ = P₁ X P₀ Y P₂` (cross-horizon duality). -/
theorem N12_commutator {T : R} (ops : NilpotentBoundaryOperators T) :
    ops.N10 * ops.N02 - ops.N02 * ops.N10 = ops.N12 := by
  rw [ops.hN10, ops.hN02, ops.hN12]
  have hP0_sq : ops.tri.P0 * ops.tri.P0 = ops.tri.P0 := (tripotent_idempotent ops.tri).2.1
  have hP2P1 : ops.tri.P2 * ops.tri.P1 = 0 := (tripotent_orthogonal ops.tri).2.2.2.1
  have hleft :
      (ops.tri.P1 * ops.X * ops.tri.P0) * (ops.tri.P0 * ops.Y * ops.tri.P2) =
        ops.tri.P1 * ops.X * ops.tri.P0 * ops.Y * ops.tri.P2 := by
    calc
      (ops.tri.P1 * ops.X * ops.tri.P0) * (ops.tri.P0 * ops.Y * ops.tri.P2)
        = ops.tri.P1 * ops.X * (ops.tri.P0 * ops.tri.P0) * ops.Y * ops.tri.P2 := by noncomm_ring
      _ = ops.tri.P1 * ops.X * ops.tri.P0 * ops.Y * ops.tri.P2 := by rw [hP0_sq]
  have hright :
      (ops.tri.P0 * ops.Y * ops.tri.P2) * (ops.tri.P1 * ops.X * ops.tri.P0) = 0 := by
    calc
      (ops.tri.P0 * ops.Y * ops.tri.P2) * (ops.tri.P1 * ops.X * ops.tri.P0)
        = ops.tri.P0 * ops.Y * (ops.tri.P2 * ops.tri.P1) * ops.X * ops.tri.P0 := by noncomm_ring
      _ = ops.tri.P0 * ops.Y * 0 * ops.X * ops.tri.P0 := by rw [hP2P1]
      _ = 0 := by noncomm_ring
  rw [hleft, hright, sub_zero]

/-- `N₁₂` lives in the contact grade `P₁ B P₂`: `P₁ N₁₂ P₂ = N₁₂`. -/
theorem N12_in_contact_grade {T : R} (ops : NilpotentBoundaryOperators T) :
    ops.tri.P1 * ops.N12 * ops.tri.P2 = ops.N12 := by
  rw [ops.hN12]
  have hP1_sq : ops.tri.P1 * ops.tri.P1 = ops.tri.P1 := (tripotent_idempotent ops.tri).1
  have hP2_sq : ops.tri.P2 * ops.tri.P2 = ops.tri.P2 := (tripotent_idempotent ops.tri).2.2
  calc
    ops.tri.P1 * (ops.tri.P1 * ops.X * ops.tri.P0 * ops.Y * ops.tri.P2) * ops.tri.P2
      = (ops.tri.P1 * ops.tri.P1) * ops.X * ops.tri.P0 * ops.Y * (ops.tri.P2 * ops.tri.P2) := by
          noncomm_ring
    _ = ops.tri.P1 * ops.X * ops.tri.P0 * ops.Y * ops.tri.P2 := by rw [hP1_sq, hP2_sq]

/-! ===========================================================================
LAYER 2: Chiral Lightcone Split (GEM (1,3)) in the P₀ Sector
=========================================================================== -/

/-- The GEM (1,3) connection in the `P₀` sector (general noncommutative carrier). -/
def GEMInP0 {T : R} (tri : TripotentTripartition T) (E B I : R) : R :=
  (tri.P0 * E * tri.P0) + (tri.P0 * I * tri.P0) * (tri.P0 * B * tri.P0)

/-- In the noncommutative `P₀` corner algebra, `P₀² = P₀` contracts the adjacent `P₀`
in `(P₀ I P₀) (P₀ B P₀)` to `P₀ I P₀ B P₀`. -/
theorem GEMInP0_simplified {T : R} (tri : TripotentTripartition T) (E B I : R) :
    GEMInP0 tri E B I = tri.P0 * E * tri.P0 + tri.P0 * I * tri.P0 * B * tri.P0 := by
  dsimp only [GEMInP0]
  have hP0_sq : tri.P0 * tri.P0 = tri.P0 := (tripotent_idempotent tri).2.1
  calc
    tri.P0 * E * tri.P0 + (tri.P0 * I * tri.P0) * (tri.P0 * B * tri.P0)
      = tri.P0 * E * tri.P0 + tri.P0 * I * (tri.P0 * tri.P0) * B * tri.P0 := by noncomm_ring
    _ = tri.P0 * E * tri.P0 + tri.P0 * I * tri.P0 * B * tri.P0 := by rw [hP0_sq]

/-- The `γ₀`-parity of GEM in `P₀`: `γ₀ F γ₀ = -(P₀ E P₀) + (P₀ I P₀) (P₀ B P₀)`. -/
theorem GEMInP0_gamma0_parity {T : R} (tri : TripotentTripartition T)
    (E B I γ₀ : R)
    (hγ₀_sq : γ₀ * γ₀ = 1)
    (hγ₀I : γ₀ * I = I * γ₀)
    (hE_odd : γ₀ * E + E * γ₀ = 0)
    (hB_even : γ₀ * B - B * γ₀ = 0)
    (hγ₀P0 : γ₀ * tri.P0 = tri.P0 * γ₀) :
    γ₀ * (GEMInP0 tri E B I) * γ₀ =
      -(tri.P0 * E * tri.P0) + (tri.P0 * I * tri.P0) * (tri.P0 * B * tri.P0) := by
  have hP0_sq : tri.P0 * tri.P0 = tri.P0 := (tripotent_idempotent tri).2.1
  have hγ₀E : γ₀ * E * γ₀ = -E := by
    have hE' : γ₀ * E = -(E * γ₀) := eq_neg_of_add_eq_zero_left hE_odd
    calc
      γ₀ * E * γ₀ = -(E * γ₀) * γ₀ := by rw [hE']
      _ = -(E * (γ₀ * γ₀)) := by rw [neg_mul, mul_assoc]
      _ = -(E * 1) := by rw [hγ₀_sq]
      _ = -E := by rw [mul_one]
  have hγ₀Iγ₀ : γ₀ * I * γ₀ = I := by
    calc
      γ₀ * I * γ₀ = I * (γ₀ * γ₀) := by rw [hγ₀I, mul_assoc]
      _ = I * 1 := by rw [hγ₀_sq]
      _ = I := mul_one _
  have hγ₀Bγ₀ : γ₀ * B * γ₀ = B := by
    have hB' : γ₀ * B = B * γ₀ := sub_eq_zero.mp hB_even
    calc
      γ₀ * B * γ₀ = B * (γ₀ * γ₀) := by rw [hB', mul_assoc]
      _ = B * 1 := by rw [hγ₀_sq]
      _ = B := mul_one _
  have h₁ : γ₀ * (tri.P0 * E * tri.P0) * γ₀ = -(tri.P0 * E * tri.P0) := by
    calc
      γ₀ * (tri.P0 * E * tri.P0) * γ₀
        = tri.P0 * (γ₀ * E * γ₀) * tri.P0 := by
            calc
              γ₀ * (tri.P0 * E * tri.P0) * γ₀
                = (γ₀ * tri.P0) * E * (tri.P0 * γ₀) := by noncomm_ring
              _ = (tri.P0 * γ₀) * E * (γ₀ * tri.P0) := by rw [hγ₀P0]
              _ = tri.P0 * (γ₀ * E * γ₀) * tri.P0 := by noncomm_ring
      _ = tri.P0 * (-E) * tri.P0 := by rw [hγ₀E]
      _ = -(tri.P0 * E * tri.P0) := by rw [mul_neg, neg_mul]
  have h₂ : γ₀ * ((tri.P0 * I * tri.P0) * (tri.P0 * B * tri.P0)) * γ₀ =
      (tri.P0 * I * tri.P0) * (tri.P0 * B * tri.P0) := by
    have hPI : γ₀ * (tri.P0 * I * tri.P0) = (tri.P0 * I * tri.P0) * γ₀ := by
      calc
        γ₀ * (tri.P0 * I * tri.P0) = (γ₀ * tri.P0) * I * tri.P0 := by noncomm_ring
        _ = tri.P0 * (γ₀ * I) * tri.P0 := by rw [hγ₀P0]; noncomm_ring
        _ = tri.P0 * I * (γ₀ * tri.P0) := by rw [hγ₀I]; noncomm_ring
        _ = (tri.P0 * I * tri.P0) * γ₀ := by rw [hγ₀P0]; noncomm_ring
    have hPB : γ₀ * (tri.P0 * B * tri.P0) = (tri.P0 * B * tri.P0) * γ₀ := by
      have hB' : γ₀ * B = B * γ₀ := sub_eq_zero.mp hB_even
      calc
        γ₀ * (tri.P0 * B * tri.P0) = (γ₀ * tri.P0) * B * tri.P0 := by noncomm_ring
        _ = tri.P0 * (γ₀ * B) * tri.P0 := by rw [hγ₀P0]; noncomm_ring
        _ = tri.P0 * B * (γ₀ * tri.P0) := by rw [hB']; noncomm_ring
        _ = (tri.P0 * B * tri.P0) * γ₀ := by rw [hγ₀P0]; noncomm_ring
    calc
      γ₀ * ((tri.P0 * I * tri.P0) * (tri.P0 * B * tri.P0)) * γ₀
        = (tri.P0 * I * tri.P0) * (γ₀ * (tri.P0 * B * tri.P0)) * γ₀ := by
            rw [← mul_assoc, hPI]; noncomm_ring
      _ = (tri.P0 * I * tri.P0) * (tri.P0 * B * tri.P0) * (γ₀ * γ₀) := by
            rw [hPB]; noncomm_ring
      _ = (tri.P0 * I * tri.P0) * (tri.P0 * B * tri.P0) := by rw [hγ₀_sq, mul_one]
  calc
    γ₀ * (GEMInP0 tri E B I) * γ₀
      = γ₀ * (tri.P0 * E * tri.P0) * γ₀ +
          γ₀ * ((tri.P0 * I * tri.P0) * (tri.P0 * B * tri.P0)) * γ₀ := by
          dsimp only [GEMInP0]
          rw [mul_add, add_mul]
    _ = -(tri.P0 * E * tri.P0) + (tri.P0 * I * tri.P0) * (tri.P0 * B * tri.P0) := by
          rw [h₁, h₂]

end TripotentLayer

/-! ===========================================================================
LAYER 3: Circular Polarized Parafermions (Z₄) from Peirce Bits
=========================================================================== -/

section ParafermionLayer

variable {R : Type*} [Ring R]

/-- The `Z₄` parafermion generator from binary carry of two Peirce bits (`realEighthRootCarry`). -/
def parafermionFromPeirceBits (P2 Φ J : R) : R :=
  realEighthRootCarry P2 Φ J

/-- Binary carry `Z₄` from two Peirce bits (via `real_eighth_root_carry_and_inverse`). -/
theorem binary_carry_z4_parafermion
    (P2 Φ J : R) (hP2 : P2 * P2 = P2) (hΦ : Φ * Φ = 1) (hJ : J * J = -1)
    (hswap : Φ * P2 = (1 - P2) * Φ) (hJP : J * P2 = P2 * J) (hJΦ : J * Φ = Φ * J) :
    parafermionFromPeirceBits P2 Φ J * parafermionFromPeirceBits P2 Φ J = J ∧
    (parafermionFromPeirceBits P2 Φ J * parafermionFromPeirceBits P2 Φ J) *
      (parafermionFromPeirceBits P2 Φ J * parafermionFromPeirceBits P2 Φ J) = -1 := by
  have hcarry := real_eighth_root_carry_and_inverse P2 Φ J hP2 hΦ hJ hswap hJP hJΦ
  exact ⟨hcarry.1, hcarry.2.1⟩

/-- The parafermion `ζ` satisfies `ζ⁴ = -1`. -/
theorem parafermion_fourth_power_neg_one
    (P2 Φ J : R) (hP2 : P2 * P2 = P2) (hΦ : Φ * Φ = 1) (hJ : J * J = -1)
    (hswap : Φ * P2 = (1 - P2) * Φ) (hJP : J * P2 = P2 * J) (hJΦ : J * Φ = Φ * J) :
    (parafermionFromPeirceBits P2 Φ J) ^ 4 = -1 := by
  have hcarry := binary_carry_z4_parafermion P2 Φ J hP2 hΦ hJ hswap hJP hJΦ
  set ζ := parafermionFromPeirceBits P2 Φ J
  calc
    ζ ^ 4 = (ζ * ζ) * (ζ * ζ) := by noncomm_ring
    _ = -1 := hcarry.2

/-- Majorana–Ivanov braid fourth-power relation vs parafermion (`ParafermionBraidBrownGaussPoset`). -/
theorem majorana_ivanov_braid_fourth_power
    (γ1 γ2 : R)
    (h1 : γ1 * γ1 = 1)
    (h2 : γ2 * γ2 = 1)
    (hAnti : γ1 * γ2 + γ2 * γ1 = 0) :
    (γ1 * γ2) * (γ1 * γ2) = -1 ∧
    ivanovMajoranaRotor γ1 γ2 * ivanovMajoranaRotor γ1 γ2 = γ1 * γ2 + γ1 * γ2 ∧
    (ivanovMajoranaRotor γ1 γ2 * ivanovMajoranaRotor γ1 γ2) *
      (ivanovMajoranaRotor γ1 γ2 * ivanovMajoranaRotor γ1 γ2) = -(1 + 1 + 1 + 1) ∧
    ivanovMajoranaRotor γ1 γ2 * (γ1 * γ2) = (γ1 * γ2) * ivanovMajoranaRotor γ1 γ2 :=
  majorana_ivanov_braid_fourth_power_neg_one_vs_parafermion γ1 γ2 h1 h2 hAnti

end ParafermionLayer

/-! ===========================================================================
LAYER 4: 4-Vector Witt Decomposition (Pin(5,5)) & Custodial Twin Exchange
=========================================================================== -/

/-- The Witt decomposition of `ℝ^{5,5}` from the `P₀` null structure. -/
structure WittDecompositionFromP0 where
  W_plus : Submodule ℝ (Fin 10 → ℝ)
  W_minus : Submodule ℝ (Fin 10 → ℝ)
  h_direct_sum : W_plus ⊔ W_minus = ⊤
  h_isotropic_plus : ∀ (x : Fin 10 → ℝ), x ∈ W_plus → kreinForm55 x x = 0
  h_isotropic_minus : ∀ (x : Fin 10 → ℝ), x ∈ W_minus → kreinForm55 x x = 0

/-- The null vectors `∞ = ½ n̄_vec`, `0 = ½ n_vec` satisfy `Q₅,₅ = 0` (`Cl55InfinityWittBoundary`). -/
theorem null_vectors_Q55_zero :
    Q55 (infinityVector55 : V55) = 0 ∧ Q55 (originVector55 : V55) = 0 :=
  ⟨infinityVector55_null, originVector55_null⟩

/-- The Clifford lifts square to zero: `∞² = 0`, `0² = 0` in `Cl(5,5)` (`Cl55InfinityWittBoundary`). -/
theorem clifford_lifts_square_zero :
    infinityClifford55 * infinityClifford55 = 0 ∧ originClifford55 * originClifford55 = 0 :=
  ⟨infinityClifford55_sq_zero, originClifford55_sq_zero⟩

/-- The CAR holds: `ι(∞)ι(0) + ι(0)ι(∞) = 1` in `Cl(5,5)` (`Cl55InfinityWittBoundary`). -/
theorem CAR_in_Cl55 :
    infinityClifford55 * originClifford55 + originClifford55 * infinityClifford55 = 1 :=
  infinity_origin_CAR_clifford

/-- Concrete `8×8` integer custodial-twin symmetry on `P₀_Z = 1 - casimirV P8_Z A8_Z A8_Z`. -/
theorem custodial_twin_exchanges_witt_8x8 :
    W_twin_Z * (1 - casimirV P8_Z A8_Z A8_Z : Matrix (Fin 8) (Fin 8) ℤ) * W_twin_Z =
      (1 - casimirV P8_Z A8_Z A8_Z : Matrix (Fin 8) (Fin 8) ℤ) := by
  have h₁ := custodial_twin_involution_Z
  rw [h₁.2.2.2.1, h₁.2.2.2.2.1]

/-- Lifted `Mat16Prod` custodial-twin invariance: `W_twin16 * P₀_16 * W_twin16 = P₀_16`. -/
theorem custodial_twin_exchanges_witt_16x16 :
    W_twin16 * (1 - (toMat8R (casimirV P8_Z A8_Z A8_Z) ⊗ₖ I2_R : Mat16Prod)) * W_twin16 =
      (1 - (toMat8R (casimirV P8_Z A8_Z A8_Z) ⊗ₖ I2_R : Mat16Prod)) := by
  let P0_Z : Matrix (Fin 8) (Fin 8) ℤ := 1 - casimirV P8_Z A8_Z A8_Z
  have hP0_form :
      (1 - (toMat8R (casimirV P8_Z A8_Z A8_Z) ⊗ₖ I2_R : Mat16Prod)) = toMat8R P0_Z ⊗ₖ I2_R := by
    rw [← one_kronecker_I2_R, ← sub_kronecker]
    congr 1
    calc
      (1 : Matrix (Fin 8) (Fin 8) ℝ) - toMat8R (casimirV P8_Z A8_Z A8_Z)
        = toMat8R 1 - toMat8R (casimirV P8_Z A8_Z A8_Z) := by rw [map_one]
      _ = toMat8R P0_Z := (map_sub toMat8R 1 (casimirV P8_Z A8_Z A8_Z)).symm
  rw [hP0_form]
  dsimp only [W_twin16]
  rw [← Matrix.mul_kronecker_mul, ← Matrix.mul_kronecker_mul, I2_R_mul_I2_R, I2_R_mul_I2_R]
  rw [← map_mul, ← map_mul, custodial_twin_exchanges_witt_8x8]

/-- Explicit T16 non-commutativity witness on `Matrix (Fin 8) (Fin 8) ℤ`. -/
theorem nullBoundary_mat8_int_noncomm_witness :
    ∃ A B : Matrix (Fin 8) (Fin 8) ℤ, A * B ≠ B * A := by
  let A : Matrix (Fin 8) (Fin 8) ℤ := Matrix.of fun i j => if i = 0 ∧ j = 0 then 1 else 0
  let B : Matrix (Fin 8) (Fin 8) ℤ := Matrix.of fun i j => if i = 0 ∧ j = 1 then 1 else 0
  refine ⟨A, B, fun h => ?_⟩
  have h01 : (A * B) 0 1 = (B * A) 0 1 := congrFun (congrFun h 0) 1
  rw [Matrix.mul_apply, Matrix.mul_apply] at h01
  simp [A, B] at h01

/-- Explicit T16 non-commutativity witness on `Matrix (Fin 2) (Fin 2) ℝ`. -/
theorem nullBoundary_mat2_real_noncomm_witness :
    ∃ A B : Matrix (Fin 2) (Fin 2) ℝ, A * B ≠ B * A := by
  refine ⟨!![1, 0; 0, 0], !![0, 1; 0, 0], fun h => ?_⟩
  have h01 := congrFun (congrFun h 0) 1
  simp [Matrix.mul_apply, Fin.sum_univ_two] at h01

/-- Explicit T16 non-commutativity witness on `Matrix (Fin 8) (Fin 8) ℝ`. -/
theorem nullBoundary_mat8_real_noncomm_witness :
    ∃ A B : Matrix (Fin 8) (Fin 8) ℝ, A * B ≠ B * A := by
  let A : Matrix (Fin 8) (Fin 8) ℝ := Matrix.of fun i j => if i = 0 ∧ j = 0 then 1 else 0
  let B : Matrix (Fin 8) (Fin 8) ℝ := Matrix.of fun i j => if i = 0 ∧ j = 1 then 1 else 0
  refine ⟨A, B, fun h => ?_⟩
  have h01 : (A * B) 0 1 = (B * A) 0 1 := congrFun (congrFun h 0) 1
  rw [Matrix.mul_apply, Matrix.mul_apply] at h01
  simp [A, B] at h01

/-- Explicit T16 non-commutativity witness on `Matrix (Fin 10) (Fin 10) ℝ`. -/
theorem nullBoundary_mat10_real_noncomm_witness :
    ∃ A B : Matrix (Fin 10) (Fin 10) ℝ, A * B ≠ B * A := by
  let A : Matrix (Fin 10) (Fin 10) ℝ := Matrix.of fun i j => if i = 0 ∧ j = 0 then 1 else 0
  let B : Matrix (Fin 10) (Fin 10) ℝ := Matrix.of fun i j => if i = 0 ∧ j = 1 then 1 else 0
  refine ⟨A, B, fun h => ?_⟩
  have h01 : (A * B) 0 1 = (B * A) 0 1 := congrFun (congrFun h 0) 1
  rw [Matrix.mul_apply, Matrix.mul_apply] at h01
  simp [A, B] at h01

/-! ===========================================================================
LAYER 5: Sewn Hilbert Boundary (Cantor H_lp) and Finite Tomita Flow
=========================================================================== -/

/-- The modular swap `J_lp` on the Cantor boundary `H_lp E` (`ConcreteHilbertSewnAnomaly`). -/
def modularSwapOnCantor {E : Type} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E] :
    H_lp E →L[ℝ] H_lp E :=
  J_lp_clm

/-- The chiral symmetry `ε_lp` on the Cantor boundary `H_lp E` (`ConcreteHilbertSewnAnomaly`). -/
def chiralSymmetryOnCantor {E : Type} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E] :
    H_lp E →L[ℝ] H_lp E :=
  epsilon_lp_clm

/-- The `Cl(1,1)` algebra on the Cantor boundary `H_lp E`. -/
theorem Cl11_on_Cantor {E : Type} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E] :
    (J_lp_clm (E := E)).comp (J_lp_clm (E := E)) = ContinuousLinearMap.id ℝ (H_lp E) ∧
    (epsilon_lp_clm (E := E)).comp (epsilon_lp_clm (E := E)) = ContinuousLinearMap.id ℝ (H_lp E) ∧
    (J_lp_clm (E := E)).comp (epsilon_lp_clm (E := E)) =
      -((epsilon_lp_clm (E := E)).comp (J_lp_clm (E := E))) :=
  ⟨J_lp_clm_comp_self, epsilon_lp_clm_comp_self, J_lp_clm_anticomm_epsilon_lp_clm⟩

/-- Sewn boundary anomaly cancellation: `⟪ψ, ε_lp(Bψ)⟫ = 0` for `J_lp`-sewn `B`. -/
theorem sewn_boundary_anomaly_cancellation
    {E : Type} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
    (B : H_lp E →L[ℝ] H_lp E)
    (hB : (J_lp_clm (E := E)).comp (B.comp (J_lp_clm (E := E))) = B)
    (ψ : H_lp E)
    (hψ : J_lp_clm (E := E) ψ = ψ) :
    inner ℝ ψ (((epsilon_lp_clm (E := E)).comp B) ψ) = 0 :=
  infinite_hilbert_sewn_chiral_expectation_zero B hB ψ hψ

/-- The `so55Boost` generates Lorentz flow preserving the null quadric. -/
theorem so55_boost_preserves_null_quadric (ξ : ℝ) (x : Fin 10 → ℝ) (hx : x ∈ NullQuadric) :
    (so55Boost ξ).mulVec x ∈ NullQuadric :=
  nullQuadric_invariant (so55Boost ξ) (so55Boost_isSO55 ξ) hx

/-- Each `so55Boost ξ` lies in `SO(5,5)`. -/
theorem modular_flow_is_so55_boost (ξ : ℝ) :
    IsSO55GroupMatrix (so55Boost ξ) :=
  so55Boost_isSO55 ξ

/-! ===========================================================================
SYNTHESIS THEOREMS
=========================================================================== -/

/-- The topological boundary is `P₀ = 1 - T * T` and annihilates `P₁, P₂`. -/
theorem nullBoundaryIsP0 {R : Type*} [Ring R] [Algebra ℝ R] {T : R}
    (tri : TripotentTripartition T) :
    tri.P0 = 1 - T * T ∧
    tri.P0 * tri.P0 = tri.P0 ∧
    tri.P1 * tri.P0 = 0 ∧
    tri.P0 * tri.P1 = 0 ∧
    tri.P2 * tri.P0 = 0 ∧
    tri.P0 * tri.P2 = 0 := by
  have h1 : tri.P0 = 1 - T * T := by rw [tri.hP0, projZero]
  have h2 : tri.P0 * tri.P0 = tri.P0 := (tripotent_idempotent tri).2.1
  have h3 : tri.P1 * tri.P0 = 0 := (tripotent_orthogonal tri).1
  have h4 : tri.P0 * tri.P1 = 0 := (tripotent_orthogonal tri).2.1
  have h5 : tri.P2 * tri.P0 = 0 := (tripotent_orthogonal tri).2.2.2.2.2
  have h6 : tri.P0 * tri.P2 = 0 := (tripotent_orthogonal tri).2.2.2.2.1
  exact ⟨h1, h2, h3, h4, h5, h6⟩

/-- The nilpotent operators `N₁₀`, `N₀₂`, `N₁₂` form the boundary algebra. -/
theorem nilpotent_boundary_operators {R : Type*} [Ring R] [Algebra ℝ R] {T : R}
    (ops : NilpotentBoundaryOperators T) :
    ops.N10 * ops.N10 = 0 ∧
    ops.N02 * ops.N02 = 0 ∧
    ops.N10 * ops.N02 - ops.N02 * ops.N10 = ops.N12 ∧
    ops.tri.P1 * ops.N12 * ops.tri.P2 = ops.N12 :=
  ⟨N10_square_zero ops, N02_square_zero ops, N12_commutator ops, N12_in_contact_grade ops⟩

/-- The GEM `(1,3)` connection lives in the `P₀` sector. -/
theorem chiral_lightcone_in_P0 {R : Type*} [Ring R] [Algebra ℝ R] {T : R}
    (tri : TripotentTripartition T) (E B I : R) :
    GEMInP0 tri E B I = tri.P0 * E * tri.P0 + tri.P0 * I * tri.P0 * B * tri.P0 :=
  GEMInP0_simplified tri E B I

/-- The `γ₀`-parity of GEM in `P₀`. -/
theorem GEMInP0_gamma0_parity_in_P0 {R : Type*} [Ring R] [Algebra ℝ R] {T : R}
    (tri : TripotentTripartition T)
    (E B I γ₀ : R)
    (hγ₀_sq : γ₀ * γ₀ = 1)
    (hγ₀I : γ₀ * I = I * γ₀)
    (hE_odd : γ₀ * E + E * γ₀ = 0)
    (hB_even : γ₀ * B - B * γ₀ = 0)
    (hγ₀P0 : γ₀ * tri.P0 = tri.P0 * γ₀) :
    γ₀ * (GEMInP0 tri E B I) * γ₀ =
      -(tri.P0 * E * tri.P0) + (tri.P0 * I * tri.P0) * (tri.P0 * B * tri.P0) :=
  GEMInP0_gamma0_parity tri E B I γ₀ hγ₀_sq hγ₀I hE_odd hB_even hγ₀P0

/-- The `Z₄` parafermion arises from binary carry of two Peirce bits. -/
theorem parafermion_from_peirce_bits {R : Type*} [Ring R] :
    ∀ (P2 Phi2 J1 : R) (_ : P2 * P2 = P2) (_ : Phi2 * Phi2 = 1) (_ : J1 * J1 = -1)
      (_ : Phi2 * P2 = (1 - P2) * Phi2) (_ : J1 * P2 = P2 * J1) (_ : J1 * Phi2 = Phi2 * J1),
      parafermionFromPeirceBits P2 Phi2 J1 * parafermionFromPeirceBits P2 Phi2 J1 = J1 ∧
      (parafermionFromPeirceBits P2 Phi2 J1 * parafermionFromPeirceBits P2 Phi2 J1) *
        (parafermionFromPeirceBits P2 Phi2 J1 * parafermionFromPeirceBits P2 Phi2 J1) = -1 := by
  intro P2 Phi2 J1 hP2 hPhi2 hJ1 hswap hJ1P2 hJ1Phi2
  exact binary_carry_z4_parafermion P2 Phi2 J1 hP2 hPhi2 hJ1 hswap hJ1P2 hJ1Phi2

/-- The Witt decomposition `ℝ^{5,5} = W₊ ⊕ W₋` null-vector CAR laws in `Cl(5,5)`. -/
theorem witt_decomposition_from_P0 :
    Q55 (infinityVector55 : V55) = 0 ∧
    Q55 (originVector55 : V55) = 0 ∧
    infinityClifford55 * infinityClifford55 = 0 ∧
    originClifford55 * originClifford55 = 0 ∧
    infinityClifford55 * originClifford55 + originClifford55 * infinityClifford55 = 1 :=
  ⟨infinityVector55_null, originVector55_null,
    infinityClifford55_sq_zero, originClifford55_sq_zero, infinity_origin_CAR_clifford⟩

/-- Sewn boundary anomaly cancellation on `H_lp E`. -/
theorem sewn_boundary_anomaly_cancellation_full
    {E : Type} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
    (B : H_lp E →L[ℝ] H_lp E)
    (hB : (J_lp_clm (E := E)).comp (B.comp (J_lp_clm (E := E))) = B)
    (ψ : H_lp E)
    (hψ : J_lp_clm (E := E) ψ = ψ) :
    inner ℝ ψ (((epsilon_lp_clm (E := E)).comp B) ψ) = 0 :=
  infinite_hilbert_sewn_chiral_expectation_zero B hB ψ hψ

/-- Finite Tomita–Takesaki / `SO(5,5)` boost flow and Cantor `Cl(1,1)` algebra. -/
theorem finite_tomita_modular_flow
    {E : Type} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E] :
    (∀ (ξ : ℝ), IsSO55GroupMatrix (so55Boost ξ)) ∧
    (∀ (x : Fin 10 → ℝ), x ∈ NullQuadric → ∀ (ξ : ℝ), (so55Boost ξ).mulVec x ∈ NullQuadric) ∧
    (J_lp_clm (E := E)).comp (J_lp_clm (E := E)) = ContinuousLinearMap.id ℝ (H_lp E) ∧
    (epsilon_lp_clm (E := E)).comp (epsilon_lp_clm (E := E)) = ContinuousLinearMap.id ℝ (H_lp E) ∧
    (J_lp_clm (E := E)).comp (epsilon_lp_clm (E := E)) =
      -((epsilon_lp_clm (E := E)).comp (J_lp_clm (E := E))) :=
  ⟨so55Boost_isSO55, fun _ hx ξ => nullQuadric_invariant (so55Boost ξ) (so55Boost_isSO55 ξ) hx,
    J_lp_clm_comp_self, epsilon_lp_clm_comp_self, J_lp_clm_anticomm_epsilon_lp_clm⟩

/-- Master synthesis: all algebraic, Clifford, Krein, and modular boundary layers unify over `P₀`. -/
theorem master_null_boundary_synthesis {R : Type*} [Ring R] [Algebra ℝ R] {T : R}
    (hT : T * T * T = T) (tri : TripotentTripartition T) :
    (tri.P1 + tri.P0 + tri.P2 = 1) ∧
    (tri.P1 * tri.P0 = 0 ∧ tri.P0 * tri.P1 = 0 ∧
     tri.P1 * tri.P2 = 0 ∧ tri.P2 * tri.P1 = 0 ∧
     tri.P0 * tri.P2 = 0 ∧ tri.P2 * tri.P0 = 0) ∧
    (tri.P1 * tri.P1 = tri.P1 ∧ tri.P0 * tri.P0 = tri.P0 ∧ tri.P2 * tri.P2 = tri.P2) ∧
    (T * tri.P1 = tri.P1 ∧ tri.P1 * T = tri.P1 ∧
     T * tri.P2 = -tri.P2 ∧ tri.P2 * T = -tri.P2 ∧
     T * tri.P0 = 0 ∧ tri.P0 * T = 0) ∧
    (tri.P0 = 1 - T * T ∧ tri.P0 * tri.P0 = tri.P0 ∧
     tri.P1 * tri.P0 = 0 ∧ tri.P0 * tri.P1 = 0 ∧
     tri.P2 * tri.P0 = 0 ∧ tri.P0 * tri.P2 = 0) ∧
    (∀ (X Y : R), let ops := canonicalNilpotentBoundaryOperators hT X Y;
      ops.N10 * ops.N10 = 0 ∧ ops.N02 * ops.N02 = 0 ∧
      ops.N10 * ops.N02 - ops.N02 * ops.N10 = ops.N12 ∧
      ops.tri.P1 * ops.N12 * ops.tri.P2 = ops.N12) ∧
    (∀ (E B I : R), GEMInP0 tri E B I = tri.P0 * E * tri.P0 + tri.P0 * I * tri.P0 * B * tri.P0) ∧
    (∀ (E B I γ₀ : R), (γ₀ * γ₀ = 1) → (γ₀ * I = I * γ₀) → (γ₀ * E + E * γ₀ = 0) →
      (γ₀ * B - B * γ₀ = 0) → (γ₀ * tri.P0 = tri.P0 * γ₀) →
      γ₀ * (GEMInP0 tri E B I) * γ₀ =
        -(tri.P0 * E * tri.P0) + (tri.P0 * I * tri.P0) * (tri.P0 * B * tri.P0)) ∧
    (Q55 (infinityVector55 : V55) = 0 ∧ Q55 (originVector55 : V55) = 0 ∧
     infinityClifford55 * infinityClifford55 = 0 ∧ originClifford55 * originClifford55 = 0 ∧
     infinityClifford55 * originClifford55 + originClifford55 * infinityClifford55 = 1) ∧
    (W_twin16 * (1 - (toMat8R (casimirV P8_Z A8_Z A8_Z) ⊗ₖ I2_R : Mat16Prod)) * W_twin16 =
      (1 - (toMat8R (casimirV P8_Z A8_Z A8_Z) ⊗ₖ I2_R : Mat16Prod))) ∧
    (∀ (ξ : ℝ), IsSO55GroupMatrix (so55Boost ξ)) :=
  ⟨tripotent_sum_eq_one tri,
    tripotent_orthogonal tri,
    tripotent_idempotent tri,
    tripotent_action tri,
    nullBoundaryIsP0 tri,
    fun X Y => nilpotent_boundary_operators (canonicalNilpotentBoundaryOperators hT X Y),
    fun E B I => chiral_lightcone_in_P0 tri E B I,
    fun E B I γ₀ h1 h2 h3 h4 h5 => GEMInP0_gamma0_parity_in_P0 tri E B I γ₀ h1 h2 h3 h4 h5,
    witt_decomposition_from_P0,
    custodial_twin_exchanges_witt_16x16,
    modular_flow_is_so55_boost⟩

end InfoGeometry.NullBoundaryTripartition
