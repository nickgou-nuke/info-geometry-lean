/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.Modular.GKSLDissipationIdentity
import InfoGeometry.Algebra.NoncommutativeCliffordPrimitives
import Mathlib.Algebra.Lie.OfAssociative
import Mathlib.Data.Matrix.Basic
import Mathlib.LinearAlgebra.Matrix.Trace
import Mathlib.Tactic

/-!
# Algebraic operator Gibbs weights and finite-step GKSL shadows

This owner contains only identities valid in arbitrary associative rings. It
reuses the division-free star-ring GKSL and carré-du-champ laws from
`GKSLDissipationIdentity`. Operator Bregman identities below are algebraic
conditional laws; they do not assert positivity, analytic Legendre duality,
operator logarithms, or a Umegaki entropy on an arbitrary ring.
-/

namespace InfoGeometry.Modular.OperatorGKSLGibbsSpinCumulants

open Matrix
open InfoGeometry.Algebra.NoncommutativeCliffordPrimitives

/-! ## Operator Boltzmann units and derivation-generated cumulants -/

section OperatorCumulants

variable {B : Type*} [Ring B]

/-- The unnormalized two-sheet partition sum associated to a unit. -/
def partitionOp (u : Bˣ) : B := (u : B) + (↑u⁻¹ : B)

/-- The unnormalized two-sheet magnetization associated to a unit. -/
def magnetOp (u : Bˣ) : B := (u : B) - (↑u⁻¹ : B)

/-- The normalized operator-valued magnetization, with the inverse partition
sum kept on the right. -/
def meanSpinOp (u Z : Bˣ) : B := magnetOp u * (↑Z⁻¹ : B)

/-- The ordered operator variance expression. -/
def varSpinOp (Z : Bˣ) : B := 4 • ((↑Z⁻¹ : B) * (↑Z⁻¹ : B))

/-- The symmetrized third-cumulant expression. -/
def skewSpinOp (u Z : Bˣ) : B :=
  -(varSpinOp Z * meanSpinOp u Z + meanSpinOp u Z * varSpinOp Z)

/-- Additive maps satisfying the Leibniz rule. -/
def IsRingDeriv (D : B →+ B) : Prop :=
  ∀ a b : B, D (a * b) = D a * b + a * D b

theorem IsRingDeriv.map_one {D : B →+ B} (hD : IsRingDeriv D) : D (1 : B) = 0 := by
  have h : D (1 : B) = D 1 + D 1 := by
    simpa only [mul_one, one_mul] using hD (1 : B) 1
  calc
    D 1 = D 1 + D 1 - D 1 := by abel
    _ = D 1 - D 1 := by rw [← h]
    _ = 0 := sub_self _

theorem IsRingDeriv.map_units_inv {D : B →+ B} (hD : IsRingDeriv D) (X : Bˣ) :
    D (↑X⁻¹ : B) = -(↑X⁻¹ : B) * D (X : B) * (↑X⁻¹ : B) := by
  have hprod := hD (X : B) (↑X⁻¹ : B)
  rw [Units.mul_inv, hD.map_one] at hprod
  have hleft := congrArg (fun z : B => (↑X⁻¹ : B) * z) hprod
  have hleft' : 0 = (↑X⁻¹ : B) * (D (X : B) * (↑X⁻¹ : B)) + D (↑X⁻¹ : B) := by
    simpa only [mul_zero, mul_add, ← mul_assoc, Units.inv_mul, one_mul] using hleft
  have hcancel : D (↑X⁻¹ : B) +
      (↑X⁻¹ : B) * (D (X : B) * (↑X⁻¹ : B)) = 0 := by
    simpa only [add_comm] using hleft'.symm
  calc
    D (↑X⁻¹ : B) = -((↑X⁻¹ : B) * (D (X : B) * (↑X⁻¹ : B))) :=
      eq_neg_of_add_eq_zero_left hcancel
    _ = -(↑X⁻¹ : B) * D (X : B) * (↑X⁻¹ : B) := by noncomm_ring

/-- Hyperbolic identity and the first three derivation-generated cumulants.
The partition unit `Z` is an explicit hypothesis: `u + u⁻¹` need not be
invertible in an arbitrary ring. -/
theorem operator_cayley_legendre_and_spin_cumulants
    {D : B →+ B} (hD : IsRingDeriv D) (u Z : Bˣ)
    (hZ : (Z : B) = partitionOp u) (hu : D (u : B) = (u : B)) :
    partitionOp u * partitionOp u - magnetOp u * magnetOp u = 4 • (1 : B) ∧
    (1 + meanSpinOp u Z) * (Z : B) = 2 • (u : B) ∧
    (1 - meanSpinOp u Z) * (Z : B) = 2 • (↑u⁻¹ : B) ∧
    1 - meanSpinOp u Z * meanSpinOp u Z = varSpinOp Z ∧
    D (↑u⁻¹ : B) = -(↑u⁻¹ : B) ∧
    D (Z : B) * (↑Z⁻¹ : B) = meanSpinOp u Z ∧
    D (meanSpinOp u Z) = varSpinOp Z ∧
    D (varSpinOp Z) = skewSpinOp u Z := by
  have hu1 : (u : B) * (↑u⁻¹ : B) = 1 := Units.mul_inv u
  have hu2 : (↑u⁻¹ : B) * (u : B) = 1 := Units.inv_mul u
  have hZ1 : (Z : B) * (↑Z⁻¹ : B) = 1 := Units.mul_inv Z
  have hZ2 : (↑Z⁻¹ : B) * (Z : B) = 1 := Units.inv_mul Z
  have h_hyp : partitionOp u * partitionOp u - magnetOp u * magnetOp u = 4 • (1 : B) := by
    dsimp [partitionOp, magnetOp]
    rw [nsmul_eq_mul]
    calc
      ((u : B) + (↑u⁻¹ : B)) * ((u : B) + (↑u⁻¹ : B)) -
          ((u : B) - (↑u⁻¹ : B)) * ((u : B) - (↑u⁻¹ : B))
        = 2 * ((u : B) * (↑u⁻¹ : B)) + 2 * ((↑u⁻¹ : B) * (u : B)) := by noncomm_ring
      _ = 4 * 1 := by rw [hu1, hu2]; norm_num
  have hZM : (Z : B) * magnetOp u = magnetOp u * (Z : B) := by
    rw [hZ]
    dsimp [partitionOp, magnetOp]
    have hcross : (u : B) * (↑u⁻¹ : B) = (↑u⁻¹ : B) * (u : B) := by
      rw [hu1, hu2]
    calc
      ((u : B) + (↑u⁻¹ : B)) * ((u : B) - (↑u⁻¹ : B))
        = (u : B) * (u : B) - (u : B) * (↑u⁻¹ : B) +
            (↑u⁻¹ : B) * (u : B) - (↑u⁻¹ : B) * (↑u⁻¹ : B) := by noncomm_ring
      _ = ((u : B) - (↑u⁻¹ : B)) * ((u : B) + (↑u⁻¹ : B)) := by
        simp only [sub_mul, mul_add]
        rw [hcross]
        abel_nf
  have hZiM : (↑Z⁻¹ : B) * magnetOp u = magnetOp u * (↑Z⁻¹ : B) := by
    calc
      (↑Z⁻¹ : B) * magnetOp u
        = (↑Z⁻¹ : B) * magnetOp u * ((Z : B) * (↑Z⁻¹ : B)) := by rw [hZ1, mul_one]
      _ = (↑Z⁻¹ : B) * (magnetOp u * (Z : B)) * (↑Z⁻¹ : B) := by noncomm_ring
      _ = (↑Z⁻¹ : B) * ((Z : B) * magnetOp u) * (↑Z⁻¹ : B) := by rw [← hZM]
      _ = ((↑Z⁻¹ : B) * (Z : B)) * magnetOp u * (↑Z⁻¹ : B) := by noncomm_ring
      _ = magnetOp u * (↑Z⁻¹ : B) := by rw [hZ2, one_mul]
  have hZsq : (Z : B) * (Z : B) * (↑Z⁻¹ : B) * (↑Z⁻¹ : B) = 1 := by
    calc
      (Z : B) * (Z : B) * (↑Z⁻¹ : B) * (↑Z⁻¹ : B)
        = (Z : B) * ((Z : B) * (↑Z⁻¹ : B)) * (↑Z⁻¹ : B) := by noncomm_ring
      _ = 1 := by rw [hZ1]; simp
  have hMprod : magnetOp u * (↑Z⁻¹ : B) * magnetOp u * (↑Z⁻¹ : B) =
      magnetOp u * magnetOp u * ((↑Z⁻¹ : B) * (↑Z⁻¹ : B)) := by
    calc
      magnetOp u * (↑Z⁻¹ : B) * magnetOp u * (↑Z⁻¹ : B)
        = magnetOp u * ((↑Z⁻¹ : B) * magnetOp u) * (↑Z⁻¹ : B) := by noncomm_ring
      _ = magnetOp u * (magnetOp u * (↑Z⁻¹ : B)) * (↑Z⁻¹ : B) := by rw [hZiM]
      _ = magnetOp u * magnetOp u * ((↑Z⁻¹ : B) * (↑Z⁻¹ : B)) := by noncomm_ring
  have h_var : 1 - meanSpinOp u Z * meanSpinOp u Z = varSpinOp Z := by
    dsimp [meanSpinOp, varSpinOp]
    have hMprod' : magnetOp u * (↑Z⁻¹ : B) *
        (magnetOp u * (↑Z⁻¹ : B)) =
        magnetOp u * magnetOp u * ((↑Z⁻¹ : B) * (↑Z⁻¹ : B)) := by
      rw [← mul_assoc, ← mul_assoc, hMprod]
      noncomm_ring
    have hfactor : (1 : B) - magnetOp u * (↑Z⁻¹ : B) *
        (magnetOp u * (↑Z⁻¹ : B)) =
        (partitionOp u * partitionOp u - magnetOp u * magnetOp u) *
          ((↑Z⁻¹ : B) * (↑Z⁻¹ : B)) := by
      rw [← hZsq, hMprod', ← hZ]
      noncomm_ring
    rw [hfactor, h_hyp]
    simp only [nsmul_eq_mul, Nat.cast_ofNat]
    noncomm_ring
  have h_invD : D (↑u⁻¹ : B) = -(↑u⁻¹ : B) := by
    rw [hD.map_units_inv u, hu]
    rw [show -(↑u⁻¹ : B) * (u : B) = -((↑u⁻¹ : B) * (u : B)) by noncomm_ring,
      hu2]
    simp
  have h_dZ : D (Z : B) = magnetOp u := by
    rw [hZ]
    dsimp [partitionOp, magnetOp]
    rw [map_add, hu, h_invD, ← sub_eq_add_neg]
  have h_dM : D (magnetOp u) = (Z : B) := by
    dsimp [magnetOp]
    rw [map_sub, hu, h_invD]
    dsimp [partitionOp] at hZ
    rw [sub_neg_eq_add]
    rw [← hZ]
  have h_deta : D (meanSpinOp u Z) = varSpinOp Z := by
    rw [← h_var]
    dsimp [meanSpinOp]
    rw [hD (magnetOp u) (↑Z⁻¹ : B), h_dM, hD.map_units_inv Z, h_dZ, hZ1]
    noncomm_ring
  have h_dZeta : D (Z : B) * (↑Z⁻¹ : B) = meanSpinOp u Z := by
    rw [h_dZ]
    rfl
  have h_skew : D (varSpinOp Z) = skewSpinOp u Z := by
    rw [← h_var, map_sub, hD.map_one, zero_sub,
      hD (meanSpinOp u Z) (meanSpinOp u Z), h_deta]
    rfl
  have h_plus : (1 + meanSpinOp u Z) * (Z : B) = 2 • (u : B) := by
    dsimp [meanSpinOp]
    rw [show (1 + magnetOp u * (↑Z⁻¹ : B)) * (Z : B) =
      (Z : B) + magnetOp u * ((↑Z⁻¹ : B) * (Z : B)) by noncomm_ring]
    rw [hZ2, mul_one, hZ]
    dsimp [partitionOp, magnetOp]
    rw [two_smul]
    abel
  constructor
  · exact h_hyp
  constructor
  · exact h_plus
  constructor
  · dsimp [meanSpinOp]
    rw [show (1 - magnetOp u * (↑Z⁻¹ : B)) * (Z : B) =
      (Z : B) - magnetOp u * ((↑Z⁻¹ : B) * (Z : B)) by noncomm_ring]
    rw [hZ2, mul_one, hZ]
    dsimp [partitionOp, magnetOp]
    rw [two_smul]
    abel
  constructor
  · exact h_var
  constructor
  · exact h_invD
  constructor
  · exact h_dZeta
  constructor
  · exact h_deta
  · exact h_skew

end OperatorCumulants

/-! ## Operator-valued two-sheet Gibbs state and discrete relaxation -/

section OperatorThermalMap

variable {B : Type*} [Ring B]

private def matrixTrace2 (X : Matrix (Fin 2) (Fin 2) B) : B := X 0 0 + X 1 1

private def fiberEmbed2 (a : B) : Matrix (Fin 2) (Fin 2) B :=
  mat2 a 0 0 a

private def projectionPlus : Matrix (Fin 2) (Fin 2) B := mat2 1 0 0 0
private def projectionMinus : Matrix (Fin 2) (Fin 2) B := mat2 0 0 0 1
private def raising : Matrix (Fin 2) (Fin 2) B := mat2 0 1 0 0
private def lowering : Matrix (Fin 2) (Fin 2) B := mat2 0 0 1 0

/-- Diagonal operator Gibbs matrix. Its entries need not be central in `B`. -/
def gibbsStateOp (wPlus wMinus : B) : Matrix (Fin 2) (Fin 2) B :=
  mat2 wPlus 0 0 wMinus

/-- Linear discrete relaxation toward the Gibbs diagonal with right-module
trace readout and left multiplication by the damping powers. -/
def markovSemigroupOp (d wPlus wMinus : B) (k : ℕ)
    (ρ : Matrix (Fin 2) (Fin 2) B) : Matrix (Fin 2) (Fin 2) B :=
  let ρeq := gibbsStateOp wPlus wMinus * fiberEmbed2 (matrixTrace2 ρ)
  ρeq + fiberEmbed2 (d ^ k) * (ρ - ρeq)

/-- KMS weight identities for an invertible `Z = u + u⁻¹`. -/
theorem operator_kms_weights (u Z : Bˣ) (hZ : (Z : B) = partitionOp u) :
    ((u : B) * (↑Z⁻¹ : B) + (↑u⁻¹ : B) * (↑Z⁻¹ : B) = 1) ∧
    ((u : B) * (↑Z⁻¹ : B) - (↑u⁻¹ : B) * (↑Z⁻¹ : B) =
      meanSpinOp u Z) ∧
    ((u : B) * (↑Z⁻¹ : B)) * (↑u⁻¹ : B) = (↑Z⁻¹ : B) ∧
    ((↑u⁻¹ : B) * (↑Z⁻¹ : B)) * (u : B) = (↑Z⁻¹ : B) := by
  have hu1 : (u : B) * (↑u⁻¹ : B) = 1 := Units.mul_inv u
  have hu2 : (↑u⁻¹ : B) * (u : B) = 1 := Units.inv_mul u
  have hZ1 : (Z : B) * (↑Z⁻¹ : B) = 1 := Units.mul_inv Z
  have hZ2 : (↑Z⁻¹ : B) * (Z : B) = 1 := Units.inv_mul Z
  have hcomm : (↑Z⁻¹ : B) * (u : B) = (u : B) * (↑Z⁻¹ : B) := by
    have huZ : (u : B) * (Z : B) = (Z : B) * (u : B) := by
      rw [hZ]
      dsimp [partitionOp]
      calc
        (u : B) * ((u : B) + (↑u⁻¹ : B))
          = (u : B) * (u : B) + (u : B) * (↑u⁻¹ : B) := by noncomm_ring
        _ = (u : B) * (u : B) + (↑u⁻¹ : B) * (u : B) := by rw [hu1, hu2]
        _ = ((u : B) + (↑u⁻¹ : B)) * (u : B) := by noncomm_ring
    calc
      (↑Z⁻¹ : B) * (u : B) = (↑Z⁻¹ : B) * (u : B) * ((Z : B) * (↑Z⁻¹ : B)) := by rw [hZ1, mul_one]
      _ = (↑Z⁻¹ : B) * ((u : B) * (Z : B)) * (↑Z⁻¹ : B) := by noncomm_ring
      _ = (↑Z⁻¹ : B) * ((Z : B) * (u : B)) * (↑Z⁻¹ : B) := by rw [huZ]
      _ = ((↑Z⁻¹ : B) * (Z : B)) * (u : B) * (↑Z⁻¹ : B) := by noncomm_ring
      _ = (u : B) * (↑Z⁻¹ : B) := by rw [hZ2, one_mul]
  refine ⟨?_, ?_, ?_, ?_⟩
  · calc
      (u : B) * (↑Z⁻¹ : B) + (↑u⁻¹ : B) * (↑Z⁻¹ : B)
        = ((u : B) + (↑u⁻¹ : B)) * (↑Z⁻¹ : B) := by rw [← add_mul]
      _ = (Z : B) * (↑Z⁻¹ : B) := by rw [hZ]; rfl
      _ = 1 := hZ1
  · dsimp [meanSpinOp, magnetOp]
    noncomm_ring
  · calc
      ((u : B) * (↑Z⁻¹ : B)) * (↑u⁻¹ : B)
        = (u : B) * ((↑Z⁻¹ : B) * (↑u⁻¹ : B)) := by noncomm_ring
      _ = (u : B) * ((↑u⁻¹ : B) * (↑Z⁻¹ : B)) := by
        have hcommInv : (↑Z⁻¹ : B) * (↑u⁻¹ : B) =
            (↑u⁻¹ : B) * (↑Z⁻¹ : B) := by
          calc
            (↑Z⁻¹ : B) * (↑u⁻¹ : B) =
                ((↑u⁻¹ : B) * (u : B)) * (↑Z⁻¹ : B) * (↑u⁻¹ : B) := by rw [hu2, one_mul]
            _ = (↑u⁻¹ : B) * ((u : B) * (↑Z⁻¹ : B)) * (↑u⁻¹ : B) := by noncomm_ring
            _ = (↑u⁻¹ : B) * ((↑Z⁻¹ : B) * (u : B)) * (↑u⁻¹ : B) := by rw [← hcomm]
            _ = (↑u⁻¹ : B) * (↑Z⁻¹ : B) * ((u : B) * (↑u⁻¹ : B)) := by noncomm_ring
            _ = (↑u⁻¹ : B) * (↑Z⁻¹ : B) := by rw [hu1, mul_one]
        rw [hcommInv]
      _ = (↑Z⁻¹ : B) := by
        calc
          (u : B) * ((↑u⁻¹ : B) * (↑Z⁻¹ : B))
            = ((u : B) * (↑u⁻¹ : B)) * (↑Z⁻¹ : B) := by noncomm_ring
          _ = (↑Z⁻¹ : B) := by rw [hu1, one_mul]
  · calc
      ((↑u⁻¹ : B) * (↑Z⁻¹ : B)) * (u : B)
        = (↑u⁻¹ : B) * ((↑Z⁻¹ : B) * (u : B)) := by noncomm_ring
      _ = (↑u⁻¹ : B) * ((u : B) * (↑Z⁻¹ : B)) := by rw [hcomm]
      _ = (↑u⁻¹ : B) * (u : B) * (↑Z⁻¹ : B) := by noncomm_ring
      _ = (↑Z⁻¹ : B) := by rw [hu2, one_mul]

/-- Stationarity of the diagonal operator Gibbs matrix for the algebraic
coherent-plus-thermal generator. The explicit commutation assumptions are
part of the statement; no positivity or complete positivity is asserted. -/
def fullThermalLindbladianOp (ωPlus ωMinus wPlus wMinus : B)
    (ρ : Matrix (Fin 2) (Fin 2) B) : Matrix (Fin 2) (Fin 2) B :=
  ⁅mat2 ωPlus 0 0 ωMinus, ρ⁆ +
    fiberEmbed2 wPlus *
      ((raising * ρ * lowering) + (raising * ρ * lowering) -
        (projectionMinus * ρ + ρ * projectionMinus)) +
    fiberEmbed2 wMinus *
      ((lowering * ρ * raising) + (lowering * ρ * raising) -
        (projectionPlus * ρ + ρ * projectionPlus))

theorem fullThermalLindbladianOp_gibbs_eq_zero
    (ωPlus ωMinus wPlus wMinus : B)
    (hww : wPlus * wMinus = wMinus * wPlus)
    (hωp : ωPlus * wPlus = wPlus * ωPlus)
    (hωm : ωMinus * wMinus = wMinus * ωMinus) :
    fullThermalLindbladianOp ωPlus ωMinus wPlus wMinus (gibbsStateOp wPlus wMinus) = 0 := by
  rw [fullThermalLindbladianOp, Ring.lie_def]
  apply ext_fin2
  · simp [gibbsStateOp, fiberEmbed2, projectionPlus, projectionMinus, raising, lowering,
      mul2_00, mul2_01, mul2_10, mul2_11]
    rw [hωp]
    simp only [mul_add, mul_neg]
    rw [hww]
    abel
  · simp [gibbsStateOp, fiberEmbed2, projectionPlus, projectionMinus, raising, lowering,
      mul2_00, mul2_01, mul2_10, mul2_11]
  · simp [gibbsStateOp, fiberEmbed2, projectionPlus, projectionMinus, raising, lowering,
      mul2_00, mul2_01, mul2_10, mul2_11]
  · simp [gibbsStateOp, fiberEmbed2, projectionPlus, projectionMinus, raising, lowering,
      mul2_00, mul2_01, mul2_10, mul2_11]
    rw [hωm]
    simp only [mul_add, mul_neg]
    rw [hww]
    abel

/-- Trace preservation and composition laws for the algebraic finite-step
relaxation. `d` need not commute with the weights: the powers act by a single
left scalar matrix and compose associatively. -/
theorem markovSemigroupOp_laws
    (d wPlus wMinus : B) (m k N : ℕ) (ρ : Matrix (Fin 2) (Fin 2) B)
    (hweights : wPlus + wMinus = 1) (hdN : d ^ N = 0) :
    markovSemigroupOp d wPlus wMinus 0 ρ = ρ ∧
    matrixTrace2 (markovSemigroupOp d wPlus wMinus k ρ) = matrixTrace2 ρ ∧
    markovSemigroupOp d wPlus wMinus m (markovSemigroupOp d wPlus wMinus k ρ) =
      markovSemigroupOp d wPlus wMinus (m + k) ρ ∧
    markovSemigroupOp d wPlus wMinus N ρ =
      gibbsStateOp wPlus wMinus * fiberEmbed2 (matrixTrace2 ρ) := by
  have htrace : ∀ n : ℕ, matrixTrace2 (markovSemigroupOp d wPlus wMinus n ρ) = matrixTrace2 ρ := by
    intro n
    dsimp [markovSemigroupOp, matrixTrace2, gibbsStateOp, fiberEmbed2]
    simp only [mat2_00, mat2_11, mul2_00, mul2_11, mat2_01, mat2_10,
      Matrix.sub_apply, mul_zero, zero_mul, add_zero, zero_add]
    have hsum : wPlus * (ρ 0 0 + ρ 1 1) + wMinus * (ρ 0 0 + ρ 1 1) = ρ 0 0 + ρ 1 1 := by
      calc
        wPlus * (ρ 0 0 + ρ 1 1) + wMinus * (ρ 0 0 + ρ 1 1)
          = (wPlus + wMinus) * (ρ 0 0 + ρ 1 1) := by noncomm_ring
        _ = ρ 0 0 + ρ 1 1 := by rw [hweights, one_mul]
    calc
      wPlus * (ρ 0 0 + ρ 1 1) +
          d ^ n * (ρ 0 0 - wPlus * (ρ 0 0 + ρ 1 1)) +
          (wMinus * (ρ 0 0 + ρ 1 1) +
            d ^ n * (ρ 1 1 - wMinus * (ρ 0 0 + ρ 1 1)))
        = (wPlus * (ρ 0 0 + ρ 1 1) + wMinus * (ρ 0 0 + ρ 1 1)) +
            d ^ n * ((ρ 0 0 + ρ 1 1) -
              (wPlus * (ρ 0 0 + ρ 1 1) + wMinus * (ρ 0 0 + ρ 1 1))) := by noncomm_ring
      _ = ρ 0 0 + ρ 1 1 := by rw [hsum, sub_self, mul_zero, add_zero]
  refine ⟨?_, htrace k, ?_, ?_⟩
  · apply ext_fin2 <;>
      simp [markovSemigroupOp, fiberEmbed2, matrixTrace2, gibbsStateOp,
        mul2_00, mul2_01, mul2_10, mul2_11]
  · let ρeq := gibbsStateOp wPlus wMinus * fiberEmbed2 (matrixTrace2 ρ)
    have htracek := htrace k
    change gibbsStateOp wPlus wMinus * fiberEmbed2
        (matrixTrace2 (markovSemigroupOp d wPlus wMinus k ρ)) +
      fiberEmbed2 (d ^ m) *
        (markovSemigroupOp d wPlus wMinus k ρ -
          gibbsStateOp wPlus wMinus * fiberEmbed2
            (matrixTrace2 (markovSemigroupOp d wPlus wMinus k ρ))) = _
    rw [htracek]
    have hmul : fiberEmbed2 (d ^ m) * fiberEmbed2 (d ^ k) = fiberEmbed2 (d ^ (m + k)) := by
      rw [pow_add]
      apply ext_fin2 <;> simp [fiberEmbed2]
    change ρeq + fiberEmbed2 (d ^ m) *
      (ρeq + fiberEmbed2 (d ^ k) * (ρ - ρeq) - ρeq) = _
    calc
      ρeq + fiberEmbed2 (d ^ m) *
          (ρeq + fiberEmbed2 (d ^ k) * (ρ - ρeq) - ρeq)
        = ρeq + (fiberEmbed2 (d ^ m) * fiberEmbed2 (d ^ k)) * (ρ - ρeq) := by noncomm_ring
      _ = ρeq + fiberEmbed2 (d ^ (m + k)) * (ρ - ρeq) := by rw [hmul]
  · dsimp [markovSemigroupOp]
    rw [hdN]
    have hzero : fiberEmbed2 (0 : B) = 0 := by
      apply ext_fin2 <;> rfl
    rw [hzero, zero_mul, add_zero]

end OperatorThermalMap

/-! ## Conditional algebraic Bregman and Spohn identities -/

section AlgebraicBregmanSpohn

variable {B : Type*} [Ring B]

def bregmanPrimalOp (ψ₁ ψ₂ θ₁ θ₂ η₂ : B) : B :=
  ψ₁ - ψ₂ - (θ₁ - θ₂) * η₂

def bregmanDualOp (φ₁ φ₂ η₁ η₂ θ₂ : B) : B :=
  φ₁ - φ₂ - θ₂ * (η₁ - η₂)

/-- Conditional noncommutative-ring algebra: reference swap, Jeffreys
symmetrization, the three-point identity, and a derivation-style Spohn law.
This is not an analytic entropy theorem: all Young identities and chain rules
are explicit hypotheses, and no order, positivity, or logarithm is supplied. -/
theorem algebraic_bregman_duality_and_spohn
    (D : B →+ B)
    (ψ φ θ η ψeq φeq θeq ηeq φ₁ φ₂ φ₃ η₁ η₂ η₃ θ₂ θ₃ γ : B)
    (hYoung : ψ + φ = θ * η) (hYoungEq : ψeq + φeq = θeq * ηeq)
    (hDφeq : D φeq = 0) (hDθeqηeq : D (θeq * ηeq) = 0)
    (hDφ : D φ = θ * D η) (hDθeqη : D (θeq * η) = θeq * D η)
    (hRelax : D η = -(η - ηeq) * γ) :
    (bregmanPrimalOp ψeq ψ θeq θ η = bregmanDualOp φ φeq η ηeq θeq ∧
      bregmanDualOp φ φeq η ηeq θeq = ψeq + φ - θeq * η) ∧
    bregmanDualOp φ φeq η ηeq θeq + bregmanDualOp φeq φ ηeq η θ =
      (θ - θeq) * (η - ηeq) ∧
    bregmanDualOp φ₁ φ₃ η₁ η₃ θ₃ =
      bregmanDualOp φ₁ φ₂ η₁ η₂ θ₂ + bregmanDualOp φ₂ φ₃ η₂ η₃ θ₃ +
        (θ₂ - θ₃) * (η₁ - η₂) ∧
    D (bregmanDualOp φ φeq η ηeq θeq) =
      -(bregmanDualOp φ φeq η ηeq θeq + bregmanDualOp φeq φ ηeq η θ) * γ := by
  have hJeff : bregmanDualOp φ φeq η ηeq θeq + bregmanDualOp φeq φ ηeq η θ =
      (θ - θeq) * (η - ηeq) := by
    dsimp [bregmanDualOp]
    noncomm_ring
  refine ⟨⟨?_, ?_⟩, hJeff, ?_, ?_⟩
  · dsimp [bregmanPrimalOp, bregmanDualOp]
    calc
      ψeq - ψ - (θeq - θ) * η =
          (ψeq + φeq - θeq * ηeq) - (ψ + φ - θ * η) +
            (φ - φeq - θeq * (η - ηeq)) := by noncomm_ring
      _ = φ - φeq - θeq * (η - ηeq) := by rw [hYoung, hYoungEq]; noncomm_ring
  · dsimp [bregmanDualOp]
    calc
      φ - φeq - θeq * (η - ηeq) =
          ψeq + φ - θeq * η - (ψeq + φeq - θeq * ηeq) := by noncomm_ring
      _ = ψeq + φ - θeq * η := by rw [hYoungEq]; noncomm_ring
  · dsimp [bregmanDualOp]
    noncomm_ring
  · dsimp [bregmanDualOp]
    have hexpand : φ - φeq - θeq * (η - ηeq) = φ - φeq - θeq * η + θeq * ηeq := by
      noncomm_ring
    dsimp [bregmanDualOp] at hJeff
    rw [hexpand, map_add, map_sub, map_sub, hDφ, hDφeq,
      hDθeqη, hDθeqηeq, hRelax]
    simp only [sub_zero, add_zero]
    calc
      θ * (-(η - ηeq) * γ) - θeq * (-(η - ηeq) * γ)
          = -((θ - θeq) * (η - ηeq)) * γ := by noncomm_ring
      _ = -(φ - φeq - θeq * (η - ηeq) + (φeq - φ - θ * (ηeq - η))) * γ :=
          congrArg (fun q : B => -q * γ) hJeff.symm
      _ = -(φ - φeq - θeq * η + θeq * ηeq +
          (φeq - φ - θ * (ηeq - η))) * γ := by rw [hexpand]

end AlgebraicBregmanSpohn

end InfoGeometry.Modular.OperatorGKSLGibbsSpinCumulants
