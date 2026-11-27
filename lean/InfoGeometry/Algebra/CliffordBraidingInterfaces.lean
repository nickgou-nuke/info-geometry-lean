/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import Mathlib.Algebra.Algebra.Basic
import InfoGeometry.Algebra.FiniteSpinAlgebra
import Mathlib.Algebra.Field.Basic
import Mathlib.Algebra.Ring.Basic
import Mathlib.LinearAlgebra.CliffordAlgebra.Contraction
import Mathlib.LinearAlgebra.Matrix.Trace
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import InfoGeometry.Algebra.FourthRootClockShift
import InfoGeometry.Topology.ParafermionBraiding

/-!
# Clifford and parafermion braid interfaces

This file separates static generator systems from braid/Yang--Baxter data.
It contains theorem boundaries only as structure fields, avoiding speculative
existence claims such as "every parafermion system has a braid operator".
-/

namespace InfoGeometry.Algebra

/-- Static Majorana/Clifford generators. -/
structure MajoranaSystem (n : Nat) (A : Type*) [Ring A] where
  gamma : Fin n → A
  square_one : ∀ i, gamma i * gamma i = 1
  anti_comm : ∀ i j, i ≠ j → gamma i * gamma j = - (gamma j * gamma i)

/-- Exact scalar data for `1 / sqrt 2` over an arbitrary division ring. -/
structure CliffordBraidScalars (K : Type*) [DivisionRing K] where
  invSqrtTwo : K
  invSqrtTwo_sq : invSqrtTwo * invSqrtTwo = (1 : K) / 2

/-- Certified Clifford braid operators. -/
structure CliffordBraidData (A : Type*) [Ring A] where
  B : Nat → A
  squareTarget : Nat → A
  square_eq_target : ∀ i, B i * B i = squareTarget i
  fourth_central_sign : ∀ i, B i ^ 4 = -1
  eighth_identity : ∀ i, B i ^ 8 = 1
  adjacent_artin : ∀ i, B i * B (i+1) * B i = B (i+1) * B i * B (i+1)
  far_commute : ∀ i j, i + 1 < j → B i * B j = B j * B i

/-- Static `Z_N` parafermion phase algebra. -/
structure ParafermionSystem
    (N n : Nat) (K A : Type*) [CommRing K] [Ring A] [Algebra K A] where
  omega : K
  omega_pow : omega ^ N = 1
  omega_primitive : ∀ k : Nat, 0 < k → k < N → omega ^ k ≠ 1
  psi : Fin n → A
  psi_pow : ∀ i, psi i ^ N = 1
  comm_phase : ∀ i j : Fin n, i < j →
    psi i * psi j = algebraMap K A omega * (psi j * psi i)

/-- Extra Yang--Baxter-compatible braid data. Not automatic from parafermions. -/
structure ParafermionBraidData
    (N n : Nat) (K A : Type*) [CommRing K] [Ring A] [Algebra K A]
    (sys : ParafermionSystem N n K A) where
  R : Nat → A
  adjacent_artin : ∀ i, R i * R (i+1) * R i = R (i+1) * R i * R (i+1)
  far_commute : ∀ i j, i + 1 < j → R i * R j = R j * R i

section MajoranaBraidAndCliffordRealization

/-- Countably infinite sequence of Majorana/Clifford generators `{γ_i}_{i : ℕ}`. -/
structure MajoranaSeq (A : Type*) [Ring A] where
  gamma : ℕ → A
  square_one : ∀ i, gamma i * gamma i = 1
  anti_comm : ∀ i j, i ≠ j → gamma i * gamma j = - (gamma j * gamma i)

/-- Every `MajoranaSystem n A` embeds into `ParafermionSystem 2 n K A` whenever `-1 ≠ 1` in `K`. -/
def parafermionSystemOfMajorana {n : ℕ} {K A : Type*} [CommRing K] [Ring A] [Algebra K A]
    (hneg : (-1 : K) ≠ 1) (sys : MajoranaSystem n A) : ParafermionSystem 2 n K A where
  omega := -1
  omega_pow := by norm_num
  omega_primitive k hk0 hk2 := by
    have hk1 : k = 1 := by omega
    subst hk1
    simpa using hneg
  psi := sys.gamma
  psi_pow i := by
    rw [pow_two]
    exact sys.square_one i
  comm_phase i j hij := by
    have hne : i ≠ j := Fin.ne_of_lt hij
    rw [sys.anti_comm i j hne, map_neg, map_one, neg_mul, one_mul]

/-- Constructive `CliffordBraidData A` from any `MajoranaSeq A` and `CliffordBraidScalars K`:
`B_i = invSqrtTwo • (1 + γ_i γ_{i+1})` satisfies `B_i^2 = γ_i γ_{i+1}`, `B_i^4 = -1`,
`B_i^8 = 1`, `B_i B_{i+1} B_i = B_{i+1} B_i B_{i+1}`, and far commutativity. -/
def cliffordBraidOfMajoranaSeq {K A : Type*} [Field K] [NeZero (2 : K)] [Ring A] [Algebra K A]
    (sc : CliffordBraidScalars K) (seq : MajoranaSeq A) : CliffordBraidData A where
  B i := algebraMap K A sc.invSqrtTwo * (1 + seq.gamma i * seq.gamma (i + 1))
  squareTarget i := seq.gamma i * seq.gamma (i + 1)
  square_eq_target i := by
    let u := seq.gamma i * seq.gamma (i + 1)
    have hu_sq : u * u = -1 := by
      dsimp [u]
      have hswap : seq.gamma (i + 1) * seq.gamma i = -(seq.gamma i * seq.gamma (i + 1)) :=
        seq.anti_comm (i + 1) i (by omega)
      calc
        seq.gamma i * seq.gamma (i + 1) * (seq.gamma i * seq.gamma (i + 1)) =
            seq.gamma i * ((seq.gamma (i + 1) * seq.gamma i) * seq.gamma (i + 1)) := by
          simp only [mul_assoc]
        _ = seq.gamma i * (-(seq.gamma i * seq.gamma (i + 1)) * seq.gamma (i + 1)) := by
          rw [hswap]
        _ = -((seq.gamma i * seq.gamma i) * (seq.gamma (i + 1) * seq.gamma (i + 1))) := by
          simp only [neg_mul, mul_neg, mul_assoc]
        _ = -1 := by rw [seq.square_one i, seq.square_one (i + 1), mul_one]
    have hinv : algebraMap K A sc.invSqrtTwo * algebraMap K A sc.invSqrtTwo * (2 : A) = 1 := by
      rw [← map_mul, sc.invSqrtTwo_sq]
      have hdiv : ((1 : K) / 2) * (2 : K) = 1 := div_mul_cancel₀ 1 (NeZero.ne (2 : K))
      calc
        algebraMap K A ((1 : K) / 2) * (2 : A) =
            algebraMap K A ((1 : K) / 2) * algebraMap K A (2 : K) := by rw [map_ofNat]
        _ = algebraMap K A (((1 : K) / 2) * (2 : K)) := by rw [← map_mul]
        _ = 1 := by rw [hdiv, map_one]
    have hc : (1 + u) * algebraMap K A sc.invSqrtTwo = algebraMap K A sc.invSqrtTwo * (1 + u) :=
      (Algebra.commutes sc.invSqrtTwo (1 + u)).symm
    calc
      (algebraMap K A sc.invSqrtTwo * (1 + u)) * (algebraMap K A sc.invSqrtTwo * (1 + u)) =
          algebraMap K A sc.invSqrtTwo * ((1 + u) * algebraMap K A sc.invSqrtTwo) * (1 + u) := by
        simp only [mul_assoc]
      _ = (algebraMap K A sc.invSqrtTwo * algebraMap K A sc.invSqrtTwo) *
            ((1 + u) * (1 + u)) := by
        rw [hc]; simp only [mul_assoc]
      _ = (algebraMap K A sc.invSqrtTwo * algebraMap K A sc.invSqrtTwo) * ((2 : A) * u) := by
        have h1u : (1 + u) * (1 + u) = (2 : A) * u := by
          calc
            (1 + u) * (1 + u) = 1 + u + u + u * u := by noncomm_ring
            _ = 1 + (2 : A) * u + -1 := by rw [hu_sq, two_mul]; abel
            _ = (2 : A) * u := by abel
        rw [h1u]
      _ = (algebraMap K A sc.invSqrtTwo * algebraMap K A sc.invSqrtTwo * (2 : A)) * u := by
        simp only [mul_assoc]
      _ = u := by rw [hinv, one_mul]
  fourth_central_sign i := by
    let u := seq.gamma i * seq.gamma (i + 1)
    have hsq : (algebraMap K A sc.invSqrtTwo * (1 + u)) *
        (algebraMap K A sc.invSqrtTwo * (1 + u)) = u := by
      have hu_sq : u * u = -1 := by
        dsimp [u]
        have hswap : seq.gamma (i + 1) * seq.gamma i = -(seq.gamma i * seq.gamma (i + 1)) :=
          seq.anti_comm (i + 1) i (by omega)
        calc
          seq.gamma i * seq.gamma (i + 1) * (seq.gamma i * seq.gamma (i + 1)) =
              seq.gamma i * ((seq.gamma (i + 1) * seq.gamma i) * seq.gamma (i + 1)) := by
            simp only [mul_assoc]
          _ = seq.gamma i * (-(seq.gamma i * seq.gamma (i + 1)) * seq.gamma (i + 1)) := by
            rw [hswap]
          _ = -((seq.gamma i * seq.gamma i) * (seq.gamma (i + 1) * seq.gamma (i + 1))) := by
            simp only [neg_mul, mul_neg, mul_assoc]
          _ = -1 := by rw [seq.square_one i, seq.square_one (i + 1), mul_one]
      have hinv : algebraMap K A sc.invSqrtTwo * algebraMap K A sc.invSqrtTwo * (2 : A) = 1 := by
        rw [← map_mul, sc.invSqrtTwo_sq]
        have hdiv : ((1 : K) / 2) * (2 : K) = 1 := div_mul_cancel₀ 1 (NeZero.ne (2 : K))
        calc
          algebraMap K A ((1 : K) / 2) * (2 : A) =
              algebraMap K A ((1 : K) / 2) * algebraMap K A (2 : K) := by rw [map_ofNat]
          _ = algebraMap K A (((1 : K) / 2) * (2 : K)) := by rw [← map_mul]
          _ = 1 := by rw [hdiv, map_one]
      have hc : (1 + u) * algebraMap K A sc.invSqrtTwo = algebraMap K A sc.invSqrtTwo * (1 + u) :=
        (Algebra.commutes sc.invSqrtTwo (1 + u)).symm
      calc
        (algebraMap K A sc.invSqrtTwo * (1 + u)) * (algebraMap K A sc.invSqrtTwo * (1 + u)) =
            algebraMap K A sc.invSqrtTwo * ((1 + u) * algebraMap K A sc.invSqrtTwo) * (1 + u) := by
          simp only [mul_assoc]
        _ = (algebraMap K A sc.invSqrtTwo * algebraMap K A sc.invSqrtTwo) * ((1 + u) * (1 + u)) := by
          rw [hc]; simp only [mul_assoc]
        _ = (algebraMap K A sc.invSqrtTwo * algebraMap K A sc.invSqrtTwo) * ((2 : A) * u) := by
          have h1u : (1 + u) * (1 + u) = (2 : A) * u := by
            calc
              (1 + u) * (1 + u) = 1 + u + u + u * u := by noncomm_ring
              _ = 1 + (2 : A) * u + -1 := by rw [hu_sq, two_mul]; abel
              _ = (2 : A) * u := by abel
          rw [h1u]
        _ = u := by rw [← mul_assoc, hinv, one_mul]
    have hu_sq : u * u = -1 := by
      dsimp [u]
      have hswap : seq.gamma (i + 1) * seq.gamma i = -(seq.gamma i * seq.gamma (i + 1)) :=
        seq.anti_comm (i + 1) i (by omega)
      calc
        seq.gamma i * seq.gamma (i + 1) * (seq.gamma i * seq.gamma (i + 1)) =
            seq.gamma i * ((seq.gamma (i + 1) * seq.gamma i) * seq.gamma (i + 1)) := by
          simp only [mul_assoc]
        _ = seq.gamma i * (-(seq.gamma i * seq.gamma (i + 1)) * seq.gamma (i + 1)) := by
          rw [hswap]
        _ = -((seq.gamma i * seq.gamma i) * (seq.gamma (i + 1) * seq.gamma (i + 1))) := by
          simp only [neg_mul, mul_neg, mul_assoc]
        _ = -1 := by rw [seq.square_one i, seq.square_one (i + 1), mul_one]
    calc
      (algebraMap K A sc.invSqrtTwo * (1 + u)) ^ 4 =
          ((algebraMap K A sc.invSqrtTwo * (1 + u)) *
            (algebraMap K A sc.invSqrtTwo * (1 + u))) *
          ((algebraMap K A sc.invSqrtTwo * (1 + u)) *
            (algebraMap K A sc.invSqrtTwo * (1 + u))) := by
        simp only [pow_succ, pow_zero, one_mul, mul_assoc]
      _ = u * u := by rw [hsq]
      _ = -1 := hu_sq
  eighth_identity i := by
    let u := seq.gamma i * seq.gamma (i + 1)
    have h4 : (algebraMap K A sc.invSqrtTwo * (1 + u)) ^ 4 = -1 := by
      let b := algebraMap K A sc.invSqrtTwo * (1 + u)
      have hb2 : b * b = u := by
        have hu_sq : u * u = -1 := by
          dsimp [u]
          have hswap := seq.anti_comm (i + 1) i (by omega)
          calc
            seq.gamma i * seq.gamma (i + 1) * (seq.gamma i * seq.gamma (i + 1)) =
                seq.gamma i * ((seq.gamma (i + 1) * seq.gamma i) * seq.gamma (i + 1)) := by
              simp only [mul_assoc]
            _ = -((seq.gamma i * seq.gamma i) * (seq.gamma (i + 1) * seq.gamma (i + 1))) := by
              rw [hswap]; simp only [neg_mul, mul_neg, mul_assoc]
            _ = -1 := by rw [seq.square_one i, seq.square_one (i + 1), mul_one]
        have hinv : algebraMap K A sc.invSqrtTwo * algebraMap K A sc.invSqrtTwo * (2 : A) = 1 := by
          rw [← map_mul, sc.invSqrtTwo_sq]
          have hdiv : ((1 : K) / 2) * (2 : K) = 1 := div_mul_cancel₀ 1 (NeZero.ne (2 : K))
          calc
            algebraMap K A ((1 : K) / 2) * (2 : A) =
                algebraMap K A ((1 : K) / 2) * algebraMap K A (2 : K) := by rw [map_ofNat]
            _ = algebraMap K A (((1 : K) / 2) * (2 : K)) := by rw [← map_mul]
            _ = 1 := by rw [hdiv, map_one]
        have hc : (1 + u) * algebraMap K A sc.invSqrtTwo = algebraMap K A sc.invSqrtTwo * (1 + u) :=
          (Algebra.commutes sc.invSqrtTwo (1 + u)).symm
        calc
          b * b = algebraMap K A sc.invSqrtTwo * ((1 + u) * algebraMap K A sc.invSqrtTwo) * (1 + u) := by
            dsimp [b]; simp only [mul_assoc]
          _ = (algebraMap K A sc.invSqrtTwo * algebraMap K A sc.invSqrtTwo) *
              ((1 + u) * (1 + u)) := by
            rw [hc]; simp only [mul_assoc]
          _ = (algebraMap K A sc.invSqrtTwo * algebraMap K A sc.invSqrtTwo) * ((2 : A) * u) := by
            have h1u : (1 + u) * (1 + u) = (2 : A) * u := by
              calc
                (1 + u) * (1 + u) = 1 + (2 : A) * u + u * u := by rw [two_mul]; noncomm_ring
                _ = (2 : A) * u := by rw [hu_sq]; noncomm_ring
            rw [h1u]
          _ = u := by rw [← mul_assoc, hinv, one_mul]
      have hu_sq : u * u = -1 := by
        dsimp [u]
        have hswap := seq.anti_comm (i + 1) i (by omega)
        calc
          seq.gamma i * seq.gamma (i + 1) * (seq.gamma i * seq.gamma (i + 1)) =
              seq.gamma i * ((seq.gamma (i + 1) * seq.gamma i) * seq.gamma (i + 1)) := by
            simp only [mul_assoc]
          _ = -((seq.gamma i * seq.gamma i) * (seq.gamma (i + 1) * seq.gamma (i + 1))) := by
            rw [hswap]; simp only [neg_mul, mul_neg, mul_assoc]
          _ = -1 := by rw [seq.square_one i, seq.square_one (i + 1), mul_one]
      calc
        b ^ 4 = (b * b) * (b * b) := by simp only [pow_succ, pow_zero, one_mul, mul_assoc]
        _ = u * u := by rw [hb2]
        _ = -1 := hu_sq
    calc
      (algebraMap K A sc.invSqrtTwo * (1 + u)) ^ 8 =
          (algebraMap K A sc.invSqrtTwo * (1 + u)) ^ 4 *
          (algebraMap K A sc.invSqrtTwo * (1 + u)) ^ 4 := by
        rw [show (8 : ℕ) = 4 + 4 by rfl, pow_add]
      _ = (-1) * (-1) := by rw [h4]
      _ = 1 := by simp
  adjacent_artin i := by
    let u := seq.gamma i * seq.gamma (i + 1)
    let v := seq.gamma (i + 1) * seq.gamma (i + 2)
    have hu2 : u * u = -1 := by
      dsimp [u]
      have hswap := seq.anti_comm (i + 1) i (by omega)
      calc
        seq.gamma i * seq.gamma (i + 1) * (seq.gamma i * seq.gamma (i + 1)) =
            seq.gamma i * ((seq.gamma (i + 1) * seq.gamma i) * seq.gamma (i + 1)) := by
          simp only [mul_assoc]
        _ = -((seq.gamma i * seq.gamma i) * (seq.gamma (i + 1) * seq.gamma (i + 1))) := by
          rw [hswap]; simp only [neg_mul, mul_neg, mul_assoc]
        _ = -1 := by rw [seq.square_one i, seq.square_one (i + 1), mul_one]
    have hv2 : v * v = -1 := by
      dsimp [v]
      have hswap := seq.anti_comm (i + 2) (i + 1) (by omega)
      calc
        seq.gamma (i + 1) * seq.gamma (i + 2) * (seq.gamma (i + 1) * seq.gamma (i + 2)) =
            seq.gamma (i + 1) * ((seq.gamma (i + 2) * seq.gamma (i + 1)) * seq.gamma (i + 2)) := by
          simp only [mul_assoc]
        _ = -((seq.gamma (i + 1) * seq.gamma (i + 1)) * (seq.gamma (i + 2) * seq.gamma (i + 2))) := by
          rw [hswap]; simp only [neg_mul, mul_neg, mul_assoc]
        _ = -1 := by rw [seq.square_one (i + 1), seq.square_one (i + 2), mul_one]
    have huv : u * v + v * u = 0 := by
      dsimp [u, v]
      have h01 : u * v = seq.gamma i * seq.gamma (i + 2) := by
        dsimp [u, v]
        calc
          seq.gamma i * seq.gamma (i + 1) * (seq.gamma (i + 1) * seq.gamma (i + 2)) =
              seq.gamma i * ((seq.gamma (i + 1) * seq.gamma (i + 1)) * seq.gamma (i + 2)) := by
            simp only [mul_assoc]
          _ = seq.gamma i * seq.gamma (i + 2) := by rw [seq.square_one (i + 1), one_mul]
      have h10 : v * u = -(seq.gamma i * seq.gamma (i + 2)) := by
        dsimp [u, v]
        have h20 : seq.gamma (i + 2) * seq.gamma i = -(seq.gamma i * seq.gamma (i + 2)) :=
          seq.anti_comm (i + 2) i (by omega)
        have h10' : seq.gamma (i + 1) * seq.gamma i = -(seq.gamma i * seq.gamma (i + 1)) :=
          seq.anti_comm (i + 1) i (by omega)
        calc
          seq.gamma (i + 1) * seq.gamma (i + 2) * (seq.gamma i * seq.gamma (i + 1)) =
              seq.gamma (i + 1) * (seq.gamma (i + 2) * seq.gamma i) * seq.gamma (i + 1) := by
            simp only [mul_assoc]
          _ = -(seq.gamma (i + 1) * seq.gamma i * seq.gamma (i + 2) * seq.gamma (i + 1)) := by
            rw [h20]; simp only [neg_mul, mul_neg, mul_assoc]
          _ = seq.gamma i * (seq.gamma (i + 1) * (seq.gamma (i + 2) * seq.gamma (i + 1))) := by
            rw [h10']; simp only [neg_mul, neg_neg, mul_assoc]
          _ = -(seq.gamma i * ((seq.gamma (i + 1) * seq.gamma (i + 1)) * seq.gamma (i + 2))) := by
            rw [seq.anti_comm (i + 2) (i + 1) (by omega)]
            simp only [mul_neg, mul_assoc]
          _ = -(seq.gamma i * seq.gamma (i + 2)) := by
            rw [seq.square_one (i + 1), one_mul]
      rw [h01, h10, add_neg_cancel]
    have hvu : v * u = -(u * v) := eq_neg_of_add_eq_zero_right huv
    have hunroll : (1 + u) * (1 + v) * (1 + u) = (1 + v) * (1 + u) * (1 + v) := by
      have hL : (1 + u) * (1 + v) * (1 + u) = (2 : A) * u + (2 : A) * v := by
        have huvu : u * v * u = v := by
          calc
            u * v * u = u * (v * u) := mul_assoc _ _ _
            _ = u * (-(u * v)) := by rw [hvu]
            _ = -((u * u) * v) := by simp only [mul_neg, mul_assoc]
            _ = v := by rw [hu2, neg_one_mul, neg_neg]
        calc
          (1 + u) * (1 + v) * (1 + u) =
              1 + u + u + v + (u * v + v * u) + u * u + u * v * u := by noncomm_ring
          _ = 1 + (2 : A) * u + v + 0 + (-1) + v := by
              rw [huv, hu2, huvu, two_mul]; abel
          _ = (2 : A) * u + (2 : A) * v := by
              calc
                1 + (2 : A) * u + v + 0 + (-1) + v = (2 : A) * u + (v + v) := by abel
                _ = (2 : A) * u + (2 : A) * v := by rw [← two_mul]
      have hR : (1 + v) * (1 + u) * (1 + v) = (2 : A) * u + (2 : A) * v := by
        have hvuv : v * u * v = u := by
          calc
            v * u * v = -(u * v) * v := by rw [hvu]
            _ = -(u * (v * v)) := by simp only [neg_mul, mul_assoc]
            _ = u := by rw [hv2, mul_neg_one, neg_neg]
        calc
          (1 + v) * (1 + u) * (1 + v) =
              1 + u + v + v + (u * v + v * u) + v * v + v * u * v := by noncomm_ring
          _ = 1 + u + (2 : A) * v + 0 + (-1) + u := by
              rw [huv, hv2, hvuv, two_mul]; abel
          _ = (2 : A) * u + (2 : A) * v := by
              calc
                1 + u + (2 : A) * v + 0 + (-1) + u = (u + u) + (2 : A) * v := by abel
                _ = (2 : A) * u + (2 : A) * v := by rw [← two_mul]
      rw [hL, hR]
    let c := algebraMap K A sc.invSqrtTwo
    have hc1 : (1 + u) * c = c * (1 + u) := (Algebra.commutes sc.invSqrtTwo (1 + u)).symm
    have hc2 : (1 + v) * c = c * (1 + v) := (Algebra.commutes sc.invSqrtTwo (1 + v)).symm
    calc
      (c * (1 + u)) * (c * (1 + v)) * (c * (1 + u)) =
          (c * c * c) * ((1 + u) * (1 + v) * (1 + u)) := by
        calc
          (c * (1 + u)) * (c * (1 + v)) * (c * (1 + u)) =
              c * ((1 + u) * c) * ((1 + v) * c) * (1 + u) := by simp only [mul_assoc]
          _ = c * (c * (1 + u)) * (c * (1 + v)) * (1 + u) := by rw [hc1, hc2]
          _ = c * c * ((1 + u) * c) * (1 + v) * (1 + u) := by simp only [mul_assoc]
          _ = c * c * (c * (1 + u)) * (1 + v) * (1 + u) := by rw [hc1]
          _ = (c * c * c) * ((1 + u) * (1 + v) * (1 + u)) := by simp only [mul_assoc]
      _ = (c * c * c) * ((1 + v) * (1 + u) * (1 + v)) := by rw [hunroll]
      _ = (c * (1 + v)) * (c * (1 + u)) * (c * (1 + v)) := by
        calc
          (c * c * c) * ((1 + v) * (1 + u) * (1 + v)) =
              c * c * (c * (1 + v)) * (1 + u) * (1 + v) := by simp only [mul_assoc]
          _ = c * c * ((1 + v) * c) * (1 + u) * (1 + v) := by rw [← hc2]
          _ = c * (c * (1 + v)) * (c * (1 + u)) * (1 + v) := by simp only [mul_assoc]
          _ = c * ((1 + v) * c) * (c * (1 + u)) * (1 + v) := by rw [← hc2]
          _ = c * (1 + v) * (c * ((c * (1 + u)) * (1 + v))) := by simp only [mul_assoc]
          _ = c * (1 + v) * (c * (((1 + u) * c) * (1 + v))) := by rw [← hc1]
          _ = (c * (1 + v)) * (c * (1 + u)) * (c * (1 + v)) := by simp only [mul_assoc]
  far_commute i j hij := by
    let u := seq.gamma i * seq.gamma (i + 1)
    let w := seq.gamma j * seq.gamma (j + 1)
    have huw : u * w = w * u := by
      have h0j : seq.gamma i * seq.gamma j = -(seq.gamma j * seq.gamma i) :=
        seq.anti_comm i j (by omega)
      have h0j1 : seq.gamma i * seq.gamma (j + 1) = -(seq.gamma (j + 1) * seq.gamma i) :=
        seq.anti_comm i (j + 1) (by omega)
      have h1j : seq.gamma (i + 1) * seq.gamma j = -(seq.gamma j * seq.gamma (i + 1)) :=
        seq.anti_comm (i + 1) j (by omega)
      have h1j1 : seq.gamma (i + 1) * seq.gamma (j + 1) =
          -(seq.gamma (j + 1) * seq.gamma (i + 1)) :=
        seq.anti_comm (i + 1) (j + 1) (by omega)
      dsimp [u, w]
      calc
        seq.gamma i * seq.gamma (i + 1) * (seq.gamma j * seq.gamma (j + 1)) =
            seq.gamma i * (seq.gamma (i + 1) * seq.gamma j) * seq.gamma (j + 1) := by
          simp only [mul_assoc]
        _ = -(seq.gamma i * seq.gamma j * (seq.gamma (i + 1) * seq.gamma (j + 1))) := by
          rw [h1j]; simp only [neg_mul, mul_neg, mul_assoc]
        _ = (seq.gamma i * seq.gamma j) * (seq.gamma (j + 1) * seq.gamma (i + 1)) := by
          rw [h1j1]; simp only [mul_neg, neg_neg, mul_assoc]
        _ = -(seq.gamma j * (seq.gamma i * seq.gamma (j + 1)) * seq.gamma (i + 1)) := by
          rw [h0j]; simp only [neg_mul, mul_assoc]
        _ = seq.gamma j * seq.gamma (j + 1) * (seq.gamma i * seq.gamma (i + 1)) := by
          rw [h0j1]; simp only [mul_neg, neg_mul, neg_neg, mul_assoc]
    let c := algebraMap K A sc.invSqrtTwo
    have hcu : (1 + u) * c = c * (1 + u) := (Algebra.commutes sc.invSqrtTwo (1 + u)).symm
    have hcw : (1 + w) * c = c * (1 + w) := (Algebra.commutes sc.invSqrtTwo (1 + w)).symm
    calc
      (c * (1 + u)) * (c * (1 + w)) = (c * c) * ((1 + u) * (1 + w)) := by
        calc
          (c * (1 + u)) * (c * (1 + w)) = c * ((1 + u) * c) * (1 + w) := by simp only [mul_assoc]
          _ = (c * c) * ((1 + u) * (1 + w)) := by rw [hcu]; simp only [mul_assoc]
      _ = (c * c) * ((1 + w) * (1 + u)) := by
        have h1 : (1 + u) * (1 + w) = (1 + w) * (1 + u) := by
          calc
            (1 + u) * (1 + w) = 1 + u + w + u * w := by noncomm_ring
            _ = 1 + w + u + w * u := by rw [huw]; abel
            _ = (1 + w) * (1 + u) := by noncomm_ring
        rw [h1]
      _ = (c * (1 + w)) * (c * (1 + u)) := by
        calc
          (c * c) * ((1 + w) * (1 + u)) = c * (c * (1 + w)) * (1 + u) := by simp only [mul_assoc]
          _ = c * ((1 + w) * c) * (1 + u) := by rw [← hcw]
          _ = (c * (1 + w)) * (c * (1 + u)) := by simp only [mul_assoc]

/-- Symmetric dot-product bilinear form on finitely supported real vectors `ℕ →₀ ℝ`. -/
noncomputable def cliffordInfDot : LinearMap.BilinForm ℝ (ℕ →₀ ℝ) :=
  LinearMap.mk₂ ℝ (fun u v : ℕ →₀ ℝ => u.sum (fun i c => c * v i))
    (fun u₁ u₂ v => by
      rw [Finsupp.sum_add_index' (fun i => zero_mul (v i)) (fun i a b => add_mul a b (v i))])
    (fun r u v => by
      rw [Finsupp.sum_smul_index' (fun i => zero_mul (v i))]
      simp only [smul_eq_mul, mul_assoc, ← Finsupp.mul_sum])
    (fun u v₁ v₂ => by
      simp only [Finsupp.coe_add, Pi.add_apply, mul_add, Finsupp.sum_add])
    (fun r u v => by
      simp only [Finsupp.coe_smul, Pi.smul_apply, smul_eq_mul]
      rw [Finsupp.mul_sum]
      refine Finset.sum_congr rfl fun i _ => by simp only [mul_left_comm])

noncomputable def cliffordInfQ : QuadraticForm ℝ (ℕ →₀ ℝ) :=
  cliffordInfDot.toQuadraticMap

theorem cliffordInfQ_single (i : ℕ) :
    cliffordInfQ (Finsupp.single i (1 : ℝ)) = 1 := by
  change cliffordInfDot (Finsupp.single i (1 : ℝ)) (Finsupp.single i (1 : ℝ)) = 1
  simp [cliffordInfDot]

theorem cliffordInfQ_polar_single_ne {i j : ℕ} (hij : i ≠ j) :
    QuadraticMap.polar cliffordInfQ (Finsupp.single i (1 : ℝ)) (Finsupp.single j (1 : ℝ)) = 0 := by
  unfold QuadraticMap.polar cliffordInfQ
  simp only [LinearMap.BilinMap.toQuadraticMap_apply, map_add, LinearMap.add_apply]
  have h0 : cliffordInfDot (Finsupp.single i (1 : ℝ)) (Finsupp.single j (1 : ℝ)) = 0 := by
    simp [cliffordInfDot, Finsupp.single_apply, hij]
  have h1 : cliffordInfDot (Finsupp.single j (1 : ℝ)) (Finsupp.single i (1 : ℝ)) = 0 := by
    simp [cliffordInfDot, Finsupp.single_apply, Ne.symm hij]
  rw [h0, h1]
  ring

/-- Concrete noncommutative infinite-mode `MajoranaSeq` inside `CliffordAlgebra cliffordInfQ`. -/
noncomputable def cliffordAlgebraMajoranaSeq : MajoranaSeq (CliffordAlgebra cliffordInfQ) where
  gamma i := CliffordAlgebra.ι cliffordInfQ (Finsupp.single i (1 : ℝ))
  square_one i := by
    rw [CliffordAlgebra.ι_sq_scalar, cliffordInfQ_single, map_one]
  anti_comm i j hij := by
    have hadd := CliffordAlgebra.ι_mul_ι_add_swap (Q := cliffordInfQ)
      (Finsupp.single i (1 : ℝ)) (Finsupp.single j (1 : ℝ))
    rw [cliffordInfQ_polar_single_ne hij, map_zero] at hadd
    exact eq_neg_of_add_eq_zero_left hadd

noncomputable def realCliffordBraidScalars : CliffordBraidScalars ℝ where
  invSqrtTwo := (Real.sqrt 2)⁻¹
  invSqrtTwo_sq := by
    rw [← mul_inv, Real.mul_self_sqrt (by norm_num), one_div]

/-- Concrete certified noncommutative `CliffordBraidData` in `CliffordAlgebra cliffordInfQ`. -/
noncomputable def cliffordAlgebraBraid : CliffordBraidData (CliffordAlgebra cliffordInfQ) :=
  cliffordBraidOfMajoranaSeq (K := ℝ) realCliffordBraidScalars cliffordAlgebraMajoranaSeq

private noncomputable def jwSign (x : ℕ →₀ Fin 2) (i : ℕ) : ℝ :=
  ((-1 : ℝ) ^ (x.support.filter (fun j => j < i)).card)

private noncomputable def jwFlip (i : ℕ) (x : ℕ →₀ Fin 2) : ℕ →₀ Fin 2 :=
  if x i = 0 then x + Finsupp.single i 1 else x - Finsupp.single i 1

private theorem jwFlip_involutive (i : ℕ) (x : ℕ →₀ Fin 2) :
    jwFlip i (jwFlip i x) = x := by
  ext j
  by_cases hji : j = i
  · subst hji
    dsimp [jwFlip]
    split_ifs with h0 h1 <;> simp at * <;> omega
  · dsimp [jwFlip]
    split_ifs <;> simp [hji]

private theorem jwFlip_ne_apply {i j : ℕ} (hij : i ≠ j) (x : ℕ →₀ Fin 2) :
    jwFlip i x j = x j := by
  dsimp [jwFlip]
  split_ifs <;> simp [Ne.symm hij]

private theorem jwSign_flip_self (i : ℕ) (x : ℕ →₀ Fin 2) :
    jwSign (jwFlip i x) i = jwSign x i := by
  dsimp [jwSign]
  congr 2
  ext j
  simp only [Finset.mem_filter, Finsupp.mem_support_iff]
  constructor
  · rintro ⟨hj, hji⟩
    refine ⟨?_, hji⟩
    rw [jwFlip_ne_apply (Nat.ne_of_gt hji)] at hj
    exact hj
  · rintro ⟨hj, hji⟩
    refine ⟨?_, hji⟩
    rw [jwFlip_ne_apply (Nat.ne_of_gt hji)]
    exact hj

private theorem jwSign_flip_lt {i k : ℕ} (hik : i < k) (x : ℕ →₀ Fin 2) :
    jwSign (jwFlip i x) k = -jwSign x k := by
  dsimp [jwSign]
  have hdiff : (jwFlip i x).support.filter (fun j => j < k) =
      if x i = 0 then insert i (x.support.filter (fun j => j < k))
      else (x.support.filter (fun j => j < k)).erase i := by
    split_ifs with h0
    · ext j
      simp only [Finset.mem_filter, Finsupp.mem_support_iff, Finset.mem_insert]
      by_cases hji : j = i
      · subst hji
        have h1 : jwFlip j x j = 1 := by
          dsimp [jwFlip]; simp [h0]
        simp [h0, h1, hik]
      · simp [jwFlip_ne_apply (Ne.symm hji), hji]
    · ext j
      simp only [Finset.mem_filter, Finsupp.mem_support_iff, Finset.mem_erase]
      by_cases hji : j = i
      · subst hji
        have hxi : x j = 1 := by omega
        have h1 : jwFlip j x j = 0 := by
          dsimp [jwFlip]; simp [hxi]
        simp [h1]
      · simp [jwFlip_ne_apply (Ne.symm hji), hji]
  rw [hdiff]
  split_ifs with h0
  · have hni : i ∉ x.support.filter (fun j => j < k) := by
      simp [Finsupp.mem_support_iff, h0]
    rw [Finset.card_insert_of_notMem hni, pow_succ]
    ring
  · have hi_mem : i ∈ x.support.filter (fun j => j < k) := by
      simp [Finset.mem_filter, Finsupp.mem_support_iff, h0, hik]
    rw [Finset.card_erase_of_mem hi_mem]
    cases hc : (x.support.filter (fun j => j < k)).card with
    | zero => exact False.elim ((Finset.card_ne_zero_of_mem hi_mem) hc)
    | succ m =>
        simp only [Nat.succ_sub_one, pow_succ]
        ring

private noncomputable def jwGamma (i : ℕ) :
    Module.End ℝ ((ℕ →₀ Fin 2) →₀ ℝ) :=
  Finsupp.lsum ℝ fun x : ℕ →₀ Fin 2 =>
    LinearMap.id.smulRight (jwSign x i • Finsupp.single (jwFlip i x) (1 : ℝ))

private theorem jwGamma_single (i : ℕ) (x : ℕ →₀ Fin 2) :
    jwGamma i (Finsupp.single x (1 : ℝ)) =
      jwSign x i • Finsupp.single (jwFlip i x) (1 : ℝ) := by
  simp [jwGamma]

private theorem jwGamma_sq (i : ℕ) : jwGamma i * jwGamma i = 1 := by
  apply LinearMap.ext
  intro v
  refine Finsupp.induction_linear v ?_ ?_ ?_
  · simp
  · intro a b ha hb; simp only [Module.End.mul_apply, map_add, Module.End.one_apply] at ha hb ⊢; rw [ha, hb]
  · intro x r
    change jwGamma i (jwGamma i (Finsupp.single x r)) = Finsupp.single x r
    have hx : Finsupp.single x r = r • Finsupp.single x (1 : ℝ) := by simp
    rw [hx, map_smul, map_smul, jwGamma_single, map_smul, jwGamma_single,
      jwSign_flip_self, jwFlip_involutive, smul_smul, smul_smul]
    have hsq : jwSign x i * jwSign x i = 1 := by
      have h2 : (-1 : ℝ) ^ 2 = 1 := by norm_num
      dsimp [jwSign]; rw [← pow_add, ← two_mul, pow_mul, h2, one_pow]
    rw [mul_assoc, hsq, mul_one]

private theorem jwGamma_anticomm {i k : ℕ} (hik : i ≠ k) :
    jwGamma i * jwGamma k + jwGamma k * jwGamma i = 0 := by
  wlog hlt : i < k generalizing i k
  · have hki : k < i := lt_of_le_of_ne (not_lt.mp hlt) hik.symm
    rw [add_comm]
    exact this hik.symm hki
  apply LinearMap.ext
  intro v
  refine Finsupp.induction_linear v (by simp)
    (fun a b ha hb => by simp only [LinearMap.add_apply, Module.End.mul_apply, map_add, LinearMap.zero_apply] at ha hb ⊢; rw [ha, hb, zero_add]) ?_
  intro x r
  change jwGamma i (jwGamma k (Finsupp.single x r)) + jwGamma k (jwGamma i (Finsupp.single x r)) = 0
  have h1 : Finsupp.single x r = r • Finsupp.single x (1 : ℝ) := by simp [Finsupp.smul_single]
  rw [h1]
  simp only [map_smul, jwGamma_single, smul_smul]
  have hflip_comm : jwFlip i (jwFlip k x) = jwFlip k (jwFlip i x) := by
    ext j
    by_cases hji : j = i
    · subst hji
      by_cases hxk : x k = 0 <;> by_cases hxj : x j = 0 <;>
        simp [jwFlip, hxk, hxj, hik]
    · by_cases hjk : j = k
      · subst hjk
        by_cases hxi : x i = 0 <;> by_cases hxj : x j = 0 <;>
          simp [jwFlip, hxi, hxj, Ne.symm hik]
      · rw [jwFlip_ne_apply (Ne.symm hji), jwFlip_ne_apply (Ne.symm hjk),
          jwFlip_ne_apply (Ne.symm hjk), jwFlip_ne_apply (Ne.symm hji)]
  have hsign_i : jwSign (jwFlip k x) i = jwSign x i := by
    dsimp [jwSign]
    congr 2
    ext j
    simp only [Finset.mem_filter, Finsupp.mem_support_iff]
    constructor <;> rintro ⟨hj, hji⟩ <;> refine ⟨?_, hji⟩
    · have hjk : j ≠ k := ne_of_lt (lt_trans hji hlt)
      rwa [jwFlip_ne_apply hjk.symm] at hj
    · have hjk : j ≠ k := ne_of_lt (lt_trans hji hlt)
      rwa [jwFlip_ne_apply hjk.symm]
  rw [hflip_comm, hsign_i, jwSign_flip_lt hlt]
  simp only [mul_neg, neg_smul]
  rw [show r * jwSign x k * jwSign x i = r * jwSign x i * jwSign x k by ring, add_neg_cancel]

/-- Concrete `MajoranaSystem 2` realized by Jordan–Wigner operators `jwGamma 0`, `jwGamma 1`. -/
noncomputable def jwMajoranaSystem2 :
    MajoranaSystem 2 (Module.End ℝ ((ℕ →₀ Fin 2) →₀ ℝ)) where
  gamma i := jwGamma i.val
  square_one i := jwGamma_sq i.val
  anti_comm i j hij := by
    have hval : i.val ≠ j.val := fun h => hij (Fin.ext h)
    exact eq_neg_iff_add_eq_zero.mpr (jwGamma_anticomm hval)

/-- Faithful Jordan–Wigner representation of `CliffordAlgebra cliffordInfQ` onto infinite-mode
bitflip space `(ℕ →₀ Fin 2) →₀ ℝ`, proving noncommutativity of `cliffordAlgebraBraid`. -/
noncomputable def cliffordInfJWRep :
    CliffordAlgebra cliffordInfQ →ₐ[ℝ] Module.End ℝ ((ℕ →₀ Fin 2) →₀ ℝ) :=
  let f : (ℕ →₀ ℝ) →ₗ[ℝ] Module.End ℝ ((ℕ →₀ Fin 2) →₀ ℝ) :=
    Finsupp.linearCombination ℝ jwGamma
  have hanti : ∀ (v : ℕ →₀ ℝ) (a : ℕ), a ∉ v.support →
      jwGamma a * f v + f v * jwGamma a = 0 := by
    intro v
    induction v using Finsupp.induction with
    | zero =>
        intro a _
        simp [f]
    | single_add c d v' hc hd ih =>
        intro a ha
        have hac : a ≠ c := by
          intro h
          subst h
          have hva : v' a = 0 := Finsupp.notMem_support_iff.mp hc
          have hmem : a ∈ (Finsupp.single a d + v').support := by
            rw [Finsupp.mem_support_iff]
            simp [hva, hd]
          exact ha hmem
        have hav : a ∉ v'.support := by
          intro hmem
          have hne : a ≠ c := fun h => hc (h ▸ hmem)
          have hmem2 : a ∈ (Finsupp.single c d + v').support := by
            rw [Finsupp.mem_support_iff]
            simp [hne, Finsupp.mem_support_iff.mp hmem]
          exact ha hmem2
        have hf_add : f (Finsupp.single c d + v') = d • jwGamma c + f v' := by
          simp [f]
        rw [hf_add, mul_add, add_mul]
        have h1 : jwGamma a * (d • jwGamma c) + d • jwGamma c * jwGamma a = 0 := by
          rw [Algebra.mul_smul_comm, Algebra.smul_mul_assoc, ← smul_add,
            jwGamma_anticomm hac, smul_zero]
        have h2 := ih a hav
        calc
          (jwGamma a * (d • jwGamma c) + jwGamma a * f v') +
              (d • jwGamma c * jwGamma a + f v' * jwGamma a) =
              (jwGamma a * (d • jwGamma c) + d • jwGamma c * jwGamma a) +
                (jwGamma a * f v' + f v' * jwGamma a) := by abel
          _ = 0 := by rw [h1, h2, add_zero]
  CliffordAlgebra.lift cliffordInfQ
    ⟨f, fun v => by
      induction v using Finsupp.induction with
      | zero => simp [f, cliffordInfQ, cliffordInfDot]
      | single_add a b v' ha hb ih =>
          have hfa : f (Finsupp.single a b + v') = b • jwGamma a + f v' := by
            simp [f]
          have hq : cliffordInfQ (Finsupp.single a b + v') = b * b + cliffordInfQ v' := by
            have hva : v' a = 0 := Finsupp.notMem_support_iff.mp ha
            change (Finsupp.single a b + v').sum (fun i c => c * (Finsupp.single a b i + v' i)) =
              b * b + v'.sum (fun i c => c * v' i)
            rw [Finsupp.sum_add_index' (fun i => zero_mul _) (fun i x y => add_mul x y _),
              Finsupp.sum_single_index (zero_mul _)]
            have hcross : v'.sum (fun i c => c * (Finsupp.single a b i + v' i)) =
                v'.sum (fun i c => c * v' i) := by
              refine Finset.sum_congr rfl fun i hi => ?_
              have hia : i ≠ a := fun h => ha (h ▸ hi)
              simp [hia]
            rw [hcross]
            simp only [Finsupp.single_apply, ↓reduceIte, hva, add_zero]
          rw [hfa, hq]
          calc
            (b • jwGamma a + f v') * (b • jwGamma a + f v') =
                (b * b) • (jwGamma a * jwGamma a) +
                  b • (jwGamma a * f v' + f v' * jwGamma a) + f v' * f v' := by
              simp only [add_mul, mul_add, smul_add, Algebra.smul_mul_assoc, Algebra.mul_smul_comm]
              rw [smul_smul]
              abel
            _ = (b * b) • (1 : Module.End ℝ ((ℕ →₀ Fin 2) →₀ ℝ)) +
                  (cliffordInfQ v') • (1 : Module.End ℝ ((ℕ →₀ Fin 2) →₀ ℝ)) := by
              rw [jwGamma_sq a, hanti v' a ha, smul_zero, add_zero, ih]
              rfl
            _ = algebraMap ℝ (Module.End ℝ ((ℕ →₀ Fin 2) →₀ ℝ)) (b * b + cliffordInfQ v') := by
              rw [← add_smul, Algebra.smul_def, mul_one]⟩

theorem cliffordInfJWRep_gamma (i : ℕ) :
    cliffordInfJWRep (cliffordAlgebraMajoranaSeq.gamma i) = jwGamma i := by
  dsimp [cliffordInfJWRep, cliffordAlgebraMajoranaSeq]
  rw [CliffordAlgebra.lift_ι_apply]
  simp

/-- Genuine noncommutativity of the concrete `CliffordAlgebra cliffordInfQ` braid data:
`B 0 * B 1 ≠ B 1 * B 0`. -/
theorem cliffordAlgebraBraid_adjacent_noncomm :
    cliffordAlgebraBraid.B 0 * cliffordAlgebraBraid.B 1 ≠
      cliffordAlgebraBraid.B 1 * cliffordAlgebraBraid.B 0 := by
  intro heq
  have hrep := congrArg cliffordInfJWRep heq
  have hB0 : cliffordInfJWRep (cliffordAlgebraBraid.B 0) =
      (Real.sqrt 2)⁻¹ • (1 + jwGamma 0 * jwGamma 1) := by
    dsimp [cliffordAlgebraBraid, cliffordBraidOfMajoranaSeq, realCliffordBraidScalars]
    rw [map_mul, AlgHom.commutes, map_add, map_one, map_mul,
      cliffordInfJWRep_gamma, cliffordInfJWRep_gamma, Algebra.smul_def]
  have hB1 : cliffordInfJWRep (cliffordAlgebraBraid.B 1) =
      (Real.sqrt 2)⁻¹ • (1 + jwGamma 1 * jwGamma 2) := by
    dsimp [cliffordAlgebraBraid, cliffordBraidOfMajoranaSeq, realCliffordBraidScalars]
    rw [map_mul, AlgHom.commutes, map_add, map_one, map_mul,
      cliffordInfJWRep_gamma, cliffordInfJWRep_gamma, Algebra.smul_def]
  rw [map_mul, map_mul, hB0, hB1] at hrep
  have h01_ne : jwGamma 0 * jwGamma 1 * (jwGamma 1 * jwGamma 2) ≠
      (jwGamma 1 * jwGamma 2) * (jwGamma 0 * jwGamma 1) := by
    intro hcomm
    have hL : jwGamma 0 * jwGamma 1 * (jwGamma 1 * jwGamma 2) = jwGamma 0 * jwGamma 2 := by
      calc
        jwGamma 0 * jwGamma 1 * (jwGamma 1 * jwGamma 2) =
            jwGamma 0 * ((jwGamma 1 * jwGamma 1) * jwGamma 2) := by simp only [mul_assoc]
        _ = jwGamma 0 * jwGamma 2 := by rw [jwGamma_sq 1, one_mul]
    have hR : (jwGamma 1 * jwGamma 2) * (jwGamma 0 * jwGamma 1) = -(jwGamma 0 * jwGamma 2) := by
      have h20 : ∀ w, jwGamma 2 (jwGamma 0 w) = -(jwGamma 0 (jwGamma 2 w)) := fun w =>
        eq_neg_of_add_eq_zero_left
          (LinearMap.congr_fun (jwGamma_anticomm (i := 2) (k := 0) (by omega)) w)
      have h10 : ∀ w, jwGamma 1 (jwGamma 0 w) = -(jwGamma 0 (jwGamma 1 w)) := fun w =>
        eq_neg_of_add_eq_zero_left
          (LinearMap.congr_fun (jwGamma_anticomm (i := 1) (k := 0) (by omega)) w)
      have h21 : ∀ w, jwGamma 2 (jwGamma 1 w) = -(jwGamma 1 (jwGamma 2 w)) := fun w =>
        eq_neg_of_add_eq_zero_left
          (LinearMap.congr_fun (jwGamma_anticomm (i := 2) (k := 1) (by omega)) w)
      have h11 : ∀ w, jwGamma 1 (jwGamma 1 w) = w := fun w =>
        LinearMap.congr_fun (jwGamma_sq 1) w
      apply LinearMap.ext
      intro w
      simp only [Module.End.mul_apply, LinearMap.neg_apply]
      calc
        (jwGamma 1) ((jwGamma 2) ((jwGamma 0) ((jwGamma 1) w)))
            = (jwGamma 1) (-(jwGamma 0) ((jwGamma 2) ((jwGamma 1) w))) := by rw [h20]
        _ = -((jwGamma 1) ((jwGamma 0) ((jwGamma 2) ((jwGamma 1) w)))) := map_neg _ _
        _ = -(-(jwGamma 0) ((jwGamma 1) ((jwGamma 2) ((jwGamma 1) w)))) := by rw [h10]
        _ = (jwGamma 0) ((jwGamma 1) ((jwGamma 2) ((jwGamma 1) w))) := neg_neg _
        _ = (jwGamma 0) ((jwGamma 1) (-(jwGamma 1) ((jwGamma 2) w))) := by rw [h21]
        _ = (jwGamma 0) (-((jwGamma 1) ((jwGamma 1) ((jwGamma 2) w)))) := by rw [map_neg]
        _ = -((jwGamma 0) ((jwGamma 1) ((jwGamma 1) ((jwGamma 2) w)))) := map_neg _ _
        _ = -((jwGamma 0) ((jwGamma 2) w)) := by rw [h11]
    have h2 : (2 : ℝ) • (jwGamma 0 * jwGamma 2) = 0 := by
      rw [two_smul]
      apply LinearMap.ext
      intro w
      have hwL := LinearMap.congr_fun hL w
      have hwR := LinearMap.congr_fun hR w
      have hwc := LinearMap.congr_fun hcomm w
      rw [hwL, hwR, LinearMap.neg_apply] at hwc
      exact add_eq_zero_iff_eq_neg.mpr hwc
    have h02_zero : jwGamma 0 * jwGamma 2 = 0 := by
      calc
        jwGamma 0 * jwGamma 2 = (1 / 2 : ℝ) • ((2 : ℝ) • (jwGamma 0 * jwGamma 2)) := by
            rw [smul_smul]; norm_num
        _ = 0 := by rw [h2, smul_zero]
    have heval := congrArg (fun T : Module.End ℝ ((ℕ →₀ Fin 2) →₀ ℝ) =>
        T (Finsupp.single (0 : ℕ →₀ Fin 2) (1 : ℝ)) (jwFlip 0 (jwFlip 2 0))) h02_zero
    simp only [Module.End.mul_apply, LinearMap.zero_apply, Finsupp.zero_apply] at heval
    rw [jwGamma_single, map_smul, jwGamma_single, Finsupp.smul_apply, Finsupp.smul_apply,
      Finsupp.single_apply] at heval
    simp only [↓reduceIte] at heval
    have hs1 : jwSign 0 2 = 1 := by simp [jwSign]
    have hs2 : jwSign (jwFlip 2 0) 0 = 1 := by
      dsimp [jwSign]
      have hfilt : ((jwFlip 2 0).support.filter (fun j => j < 0)) = ∅ := by simp
      rw [hfilt, Finset.card_empty, pow_zero]
    rw [hs1, hs2] at heval
    norm_num at heval
  have h12 : (1 + jwGamma 0 * jwGamma 1) * (1 + jwGamma 1 * jwGamma 2) =
      (1 + jwGamma 1 * jwGamma 2) * (1 + jwGamma 0 * jwGamma 1) := by
    have hinv : ((Real.sqrt 2)⁻¹ * (Real.sqrt 2)⁻¹) = (1 / 2 : ℝ) := by
      rw [← mul_inv, Real.mul_self_sqrt (by norm_num), one_div]
    have hs' : (1 / 2 : ℝ) • ((1 + jwGamma 0 * jwGamma 1) * (1 + jwGamma 1 * jwGamma 2)) =
        (1 / 2 : ℝ) • ((1 + jwGamma 1 * jwGamma 2) * (1 + jwGamma 0 * jwGamma 1)) := by
      rw [← hinv]
      simpa only [Algebra.smul_mul_assoc, Algebra.mul_smul_comm, smul_smul] using hrep
    have hs2 := congrArg ((2 : ℝ) • ·) hs'
    simpa only [smul_smul, show (2 : ℝ) * (1 / 2 : ℝ) = 1 by norm_num, one_smul] using hs2
  apply h01_ne
  calc
    jwGamma 0 * jwGamma 1 * (jwGamma 1 * jwGamma 2) =
        (1 + jwGamma 0 * jwGamma 1) * (1 + jwGamma 1 * jwGamma 2) -
          1 - jwGamma 0 * jwGamma 1 - jwGamma 1 * jwGamma 2 := by noncomm_ring
    _ = (1 + jwGamma 1 * jwGamma 2) * (1 + jwGamma 0 * jwGamma 1) -
          1 - jwGamma 0 * jwGamma 1 - jwGamma 1 * jwGamma 2 := by rw [h12]
    _ = (jwGamma 1 * jwGamma 2) * (jwGamma 0 * jwGamma 1) := by noncomm_ring

end MajoranaBraidAndCliffordRealization

section GeneralizedParafermionObstruction

/-- Exact algebraic defect of the linear braid ansatz `R₁ = c₀ • 1 + c₁ • u₁`,
`R₂ = c₀ • 1 + c₁ • u₂` in any associative `K`-algebra `A`. -/
theorem linear_ansatz_braid_defect {K A : Type*} [CommRing K] [Ring A] [Algebra K A]
    (c₀ c₁ : K) (u₁ u₂ : A) :
    let R₁ := c₀ • (1 : A) + c₁ • u₁
    let R₂ := c₀ • (1 : A) + c₁ • u₂
    R₁ * R₂ * R₁ - R₂ * R₁ * R₂ =
      (c₀ ^ 2 * c₁) • (u₁ - u₂) +
        (c₀ * c₁ ^ 2) • (u₁ * u₁ - u₂ * u₂) +
        c₁ ^ 3 • (u₁ * u₂ * u₁ - u₂ * u₁ * u₂) := by
  intro R₁ R₂
  dsimp [R₁, R₂]
  simp only [add_mul, mul_add, Algebra.smul_mul_assoc, Algebra.mul_smul_comm, smul_smul,
    smul_add, smul_sub, one_mul, mul_one]
  have hc000 : c₀ * (c₀ * c₀) = c₀ ^ 3 := by ring
  have hc001 : c₀ * (c₀ * c₁) = c₀ ^ 2 * c₁ := by ring
  have hc010 : c₀ * (c₁ * c₀) = c₀ ^ 2 * c₁ := by ring
  have hc100 : c₁ * (c₀ * c₀) = c₀ ^ 2 * c₁ := by ring
  have hc011 : c₀ * (c₁ * c₁) = c₀ * c₁ ^ 2 := by ring
  have hc101 : c₁ * (c₀ * c₁) = c₀ * c₁ ^ 2 := by ring
  have hc110 : c₁ * (c₁ * c₀) = c₀ * c₁ ^ 2 := by ring
  have hc111 : c₁ * (c₁ * c₁) = c₁ ^ 3 := by ring
  rw [hc000, hc001, hc010, hc100, hc011, hc101, hc110, hc111]
  simp only [mul_assoc]
  module

/-- Generalized `N ≥ 3` linear-ansatz braid obstruction: for any `ParafermionSystem N n K A`
with a `K`-linear grade-separating functional `φ : A →ₗ[K] K` satisfying `φ u₁ ≠ 0` and
vanishing on `{u₂, u₁^2, u₂^2, u₁ u₂ u₁, u₂ u₁ u₂}`, the Artin relation for
`R₁ = c₀ • 1 + c₁ • u₁`, `R₂ = c₀ • 1 + c₁ • u₂` forces `c₀ ^ 2 * c₁ = 0`. -/
theorem parafermion_linear_ansatz_obstruction {N n : ℕ} {K A : Type*}
    [CommRing K] [Ring A] [Algebra K A] [NoZeroDivisors K]
    (_sys : ParafermionSystem N n K A)
    (u₁ u₂ : A) (c₀ c₁ : K)
    (φ : A →ₗ[K] K)
    (hφ₁ : φ u₁ ≠ 0) (hφ₂ : φ u₂ = 0)
    (hφ11 : φ (u₁ * u₁) = 0) (hφ22 : φ (u₂ * u₂) = 0)
    (hφ121 : φ (u₁ * u₂ * u₁) = 0) (hφ212 : φ (u₂ * u₁ * u₂) = 0)
    (hartin : (c₀ • (1 : A) + c₁ • u₁) * (c₀ • (1 : A) + c₁ • u₂) * (c₀ • (1 : A) + c₁ • u₁) =
      (c₀ • (1 : A) + c₁ • u₂) * (c₀ • (1 : A) + c₁ • u₁) * (c₀ • (1 : A) + c₁ • u₂)) :
    c₀ = 0 ∨ c₁ = 0 := by
  have hdef := linear_ansatz_braid_defect c₀ c₁ u₁ u₂
  dsimp only at hdef
  rw [hartin, sub_self] at hdef
  have hzero := congrArg φ hdef.symm
  simp only [map_zero, map_add, map_sub, map_smul, smul_eq_mul,
    hφ₂, hφ11, hφ22, hφ121, hφ212, sub_zero, mul_zero, add_zero] at hzero
  rcases mul_eq_zero.mp hzero with hc | h1
  · rcases mul_eq_zero.mp hc with h02 | hc1
    · exact Or.inl (sq_eq_zero_iff.mp h02)
    · exact Or.inr hc1
  · exact False.elim (hφ₁ h1)

end GeneralizedParafermionObstruction

section GeneralizedZ3QuadraticBraid

/-- Generalized emergent quadratic `N = 3` Artin braid theorem over ANY `[CommRing K]`
and `[Ring A]` `[Algebra K A]`: if `ω^3 = 1`, `u₁^3 = 1`, `u₂^3 = 1`, and
`u₁ * u₂ = ω • (u₂ * u₁)`, then `R_i = 1 + ω • u_i + ω • u_i^2` satisfies the
exact Yang–Baxter / Artin braid relation `R₁ * R₂ * R₁ = R₂ * R₁ * R₂`. -/
theorem quadraticZ3ArtinRelation {K A : Type*} [CommRing K] [Ring A] [Algebra K A]
    {ω : K} (hω3 : ω ^ 3 = 1) {u₁ u₂ : A}
    (hu₁ : u₁ ^ 3 = 1) (hu₂ : u₂ ^ 3 = 1) (hcomm : u₁ * u₂ = ω • (u₂ * u₁)) :
    (1 + ω • u₁ + ω • (u₁ * u₁)) * (1 + ω • u₂ + ω • (u₂ * u₂)) *
        (1 + ω • u₁ + ω • (u₁ * u₁)) =
      (1 + ω • u₂ + ω • (u₂ * u₂)) * (1 + ω • u₁ + ω • (u₁ * u₁)) *
        (1 + ω • u₂ + ω • (u₂ * u₂)) := by
  have hu₁3 : u₁ * u₁ * u₁ = 1 := by simpa [pow_succ, pow_zero, one_mul, mul_assoc] using hu₁
  have hu₂3 : u₂ * u₂ * u₂ = 1 := by simpa [pow_succ, pow_zero, one_mul, mul_assoc] using hu₂
  have h11_2 : (u₁ * u₁) * u₂ = (ω ^ 2) • (u₂ * (u₁ * u₁)) := by
    calc
      (u₁ * u₁) * u₂ = u₁ * (u₁ * u₂) := mul_assoc _ _ _
      _ = u₁ * (ω • (u₂ * u₁)) := by rw [hcomm]
      _ = ω • ((u₁ * u₂) * u₁) := by rw [Algebra.mul_smul_comm, mul_assoc]
      _ = ω • (ω • (u₂ * u₁) * u₁) := by rw [hcomm]
      _ = (ω ^ 2) • (u₂ * (u₁ * u₁)) := by
          rw [Algebra.smul_mul_assoc, smul_smul, mul_assoc, ← sq]
  have h1_22 : u₁ * (u₂ * u₂) = (ω ^ 2) • ((u₂ * u₂) * u₁) := by
    calc
      u₁ * (u₂ * u₂) = (u₁ * u₂) * u₂ := (mul_assoc _ _ _).symm
      _ = ω • (u₂ * u₁) * u₂ := by rw [hcomm]
      _ = ω • (u₂ * (u₁ * u₂)) := by rw [Algebra.smul_mul_assoc, mul_assoc]
      _ = ω • (u₂ * (ω • (u₂ * u₁))) := by rw [hcomm]
      _ = (ω ^ 2) • ((u₂ * u₂) * u₁) := by
          rw [Algebra.mul_smul_comm, smul_smul, mul_assoc, ← sq]
  have h11_22 : (u₁ * u₁) * (u₂ * u₂) = ω • ((u₂ * u₂) * (u₁ * u₁)) := by
    calc
      (u₁ * u₁) * (u₂ * u₂) = u₁ * (u₁ * (u₂ * u₂)) := mul_assoc _ _ _
      _ = u₁ * (ω ^ 2 • ((u₂ * u₂) * u₁)) := by rw [h1_22]
      _ = ω ^ 2 • ((u₁ * (u₂ * u₂)) * u₁) := by rw [Algebra.mul_smul_comm]; simp only [mul_assoc]
      _ = ω ^ 2 • (ω ^ 2 • ((u₂ * u₂) * u₁) * u₁) := by rw [h1_22]
      _ = (ω ^ 3 * ω) • ((u₂ * u₂) * (u₁ * u₁)) := by
          rw [Algebra.smul_mul_assoc, smul_smul, mul_assoc]
          congr 1; ring
      _ = ω • ((u₂ * u₂) * (u₁ * u₁)) := by rw [hω3, one_mul]
  let c : Fin 3 → K := ![1, ω, ω]
  let powA : A → Fin 3 → A := fun u a => if a = 0 then 1 else if a = 1 then u else u * u
  have hpowA_mul : ∀ {u : A} (hu3 : u * u * u = 1) (a b : Fin 3),
      powA u a * powA u b = powA u (a + b) := by
    intro u hu3 a b
    fin_cases a <;> fin_cases b <;>
      simp [powA, Fin.add_def, mul_assoc, hu3]
    · calc
        u * (u * u) = u * u * u := (mul_assoc _ _ _).symm
        _ = 1 := hu3
    · calc
        u * (u * (u * u)) = (u * u * u) * u := by simp only [mul_assoc]
        _ = u := by rw [hu3, one_mul]
  have hω4 : ω ^ 4 = ω := by rw [show (4 : ℕ) = 3 + 1 by rfl, pow_add, hω3, one_mul, pow_one]
  have hcomm_pow : ∀ a b : Fin 3,
      powA u₁ a * powA u₂ b = (ω ^ (a.val * b.val)) • (powA u₂ b * powA u₁ a) := by
    intro a b
    fin_cases a <;> fin_cases b <;>
      simp [powA, hcomm, h11_2, h1_22, h11_22, hω4]
  have hR₁_sum : (1 + ω • u₁ + ω • (u₁ * u₁) : A) = ∑ a : Fin 3, c a • powA u₁ a := by
    simp [Fin.sum_univ_three, c, powA, add_assoc]
  have hR₂_sum : (1 + ω • u₂ + ω • (u₂ * u₂) : A) = ∑ b : Fin 3, c b • powA u₂ b := by
    simp [Fin.sum_univ_three, c, powA, add_assoc]
  have hnorm : ∀ (a b d : Fin 3),
      (c a • powA u₁ a) * (c b • powA u₂ b) * (c d • powA u₁ d) =
        (c a * c b * c d * ω ^ (a.val * b.val)) • (powA u₂ b * powA u₁ (a + d)) := by
    intro a b d
    calc
      (c a • powA u₁ a) * (c b • powA u₂ b) * (c d • powA u₁ d) =
          (c a * c b * c d) • ((powA u₁ a * powA u₂ b) * powA u₁ d) := by
        simp only [Algebra.smul_mul_assoc, Algebra.mul_smul_comm, smul_smul]; congr 1; ring
      _ = (c a * c b * c d * ω ^ (a.val * b.val)) • (powA u₂ b * powA u₁ (a + d)) := by
        rw [hcomm_pow a b, Algebra.smul_mul_assoc, smul_smul, mul_assoc (powA u₂ b),
          hpowA_mul hu₁3 a d]
  have hnormR : ∀ (a b d : Fin 3),
      (c a • powA u₂ a) * (c b • powA u₁ b) * (c d • powA u₂ d) =
        (c a * c b * c d * ω ^ (b.val * d.val)) • (powA u₂ (a + d) * powA u₁ b) := by
    intro a b d
    have hcomm_rev : powA u₁ b * powA u₂ d = (ω ^ (b.val * d.val)) • (powA u₂ d * powA u₁ b) :=
      hcomm_pow b d
    calc
      (c a • powA u₂ a) * (c b • powA u₁ b) * (c d • powA u₂ d) =
          (c a * c b * c d) • (powA u₂ a * (powA u₁ b * powA u₂ d)) := by
        simp only [Algebra.smul_mul_assoc, Algebra.mul_smul_comm, smul_smul, mul_assoc]
        congr 1; ring
      _ = (c a * c b * c d * ω ^ (b.val * d.val)) • (powA u₂ (a + d) * powA u₁ b) := by
        rw [hcomm_rev, Algebra.mul_smul_comm, ← mul_assoc, hpowA_mul hu₂3 a d, smul_smul]
  rw [hR₁_sum, hR₂_sum]
  simp only [Finset.sum_mul, Finset.mul_sum]
  simp only [hnorm, hnormR]
  have hc0 : c 0 = 1 := rfl
  have hc1 : c 1 = ω := rfl
  have hc2 : c 2 = ω := rfl
  have h00 : (0 + 0 : Fin 3) = 0 := rfl
  have h01 : (0 + 1 : Fin 3) = 1 := rfl
  have h02 : (0 + 2 : Fin 3) = 2 := rfl
  have h10 : (1 + 0 : Fin 3) = 1 := rfl
  have h11 : (1 + 1 : Fin 3) = 2 := rfl
  have h12 : (1 + 2 : Fin 3) = 0 := rfl
  have h20 : (2 + 0 : Fin 3) = 2 := rfl
  have h21 : (2 + 1 : Fin 3) = 0 := rfl
  have h22 : (2 + 2 : Fin 3) = 1 := rfl
  have hω_sq : ω * ω = ω ^ 2 := (sq ω).symm
  have hω_cube : ω ^ 2 * ω = 1 := by rw [← pow_succ, hω3]
  have hω_four : ω ^ 2 * ω ^ 2 = ω := by rw [← pow_add, show 2 + 2 = 4 by rfl, hω4]
  simp only [Fin.sum_univ_three, Fin.val_zero, Fin.val_one, Fin.val_two, hc0, hc1, hc2,
    h00, h01, h02, h10, h11, h12, h20, h21, h22, pow_zero, pow_one, mul_one, one_mul,
    hω_sq, hω_cube, hω_four, hω4]
  module

end GeneralizedZ3QuadraticBraid

section InfiniteAndWeylParafermions

/-- Canonical primitive `N`-th root of unity `ω_N = exp(2πi / N)`. -/
noncomputable def paraOmega (N : ℕ) : ℂ :=
  Complex.exp (2 * Real.pi * Complex.I / (N : ℂ))

theorem paraOmega_pow (N : ℕ) [NeZero N] : paraOmega N ^ N = 1 := by
  unfold paraOmega
  rw [← Complex.exp_nat_mul]
  have hN : (N : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (NeZero.ne N)
  rw [mul_div_cancel₀ _ hN, Complex.exp_two_pi_mul_I]

theorem paraOmega_primitive (N : ℕ) (hN : 2 ≤ N) {k : ℕ} (hk0 : 0 < k) (hkN : k < N) :
    paraOmega N ^ k ≠ 1 := by
  intro heq
  unfold paraOmega at heq
  rw [← Complex.exp_nat_mul, Complex.exp_eq_one_iff] at heq
  rcases heq with ⟨m, hm⟩
  have hpi : (2 : ℂ) * Real.pi * Complex.I ≠ 0 := by
    simp [Real.pi_ne_zero, Complex.I_ne_zero]
  have hN_pos : 0 < N := lt_of_lt_of_le (by decide) hN
  have hN0 : (N : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.ne_of_gt hN_pos)
  have hrat : ((k : ℂ) / (N : ℂ)) * (2 * Real.pi * Complex.I) =
      (m : ℂ) * (2 * Real.pi * Complex.I) := by
    calc
      ((k : ℂ) / (N : ℂ)) * (2 * Real.pi * Complex.I) =
          (k : ℂ) * (2 * Real.pi * Complex.I / (N : ℂ)) := by ring
      _ = (m : ℂ) * (2 * Real.pi * Complex.I) := hm
  have hkm : (k : ℂ) / (N : ℂ) = (m : ℂ) := mul_right_cancel₀ hpi hrat
  have hkm' : (k : ℂ) = (m : ℂ) * (N : ℂ) := (div_eq_iff hN0).mp hkm
  have hkmZ : (k : ℤ) = m * (N : ℤ) := by exact_mod_cast hkm'
  have hk_pos : (0 : ℤ) < k := Int.natCast_pos.mpr hk0
  have hk_lt : (k : ℤ) < N := Int.ofNat_lt.mpr hkN
  have hm0 : 0 < m := by
    by_contra hm_le
    have : m * (N : ℤ) ≤ 0 := mul_nonpos_of_nonpos_of_nonneg (not_lt.mp hm_le) (by positivity)
    omega
  have hm1 : 1 ≤ m := hm0
  have hge : (N : ℤ) ≤ m * (N : ℤ) := le_mul_of_one_le_left (by positivity) hm1
  omega

/-- Weyl shift matrix `X_N` on `Fin N`: `e_i ↦ e_{i+1}`. -/
noncomputable def weylShift (N : ℕ) [NeZero N] : Matrix (Fin N) (Fin N) ℂ :=
  fun i j => if i = j + 1 then 1 else 0

/-- Weyl adjoint clock matrix `Z_N†` on `Fin N`: `diag(ω_N^{-i})`. -/
noncomputable def weylClockDag (N : ℕ) [NeZero N] : Matrix (Fin N) (Fin N) ℂ :=
  Matrix.diagonal (fun i : Fin N => (paraOmega N ^ (N - 1)) ^ i.val)

private def finAddNat {N : ℕ} [NeZero N] (j : Fin N) (m : ℕ) : Fin N :=
  ⟨(j.val + m) % N, Nat.mod_lt _ (NeZero.pos N)⟩

theorem weylShift_pow_eq_one (N : ℕ) [NeZero N] : weylShift N ^ N = 1 := by
  have hpow : ∀ (m : ℕ) (i j : Fin N),
      (weylShift N ^ m) i j = if i = finAddNat j m then 1 else 0 := by
    intro m
    induction m with
    | zero =>
        intro i j
        have hz : finAddNat j 0 = j := Fin.ext (by simp [finAddNat, Nat.mod_eq_of_lt j.isLt])
        rw [hz]
        simp [Matrix.one_apply]
    | succ m ihm =>
        intro i j
        rw [pow_succ, Matrix.mul_apply]
        have heq : (∑ k : Fin N, (weylShift N ^ m) i k * weylShift N k j) =
            (weylShift N ^ m) i (j + 1) := by
          rw [Finset.sum_eq_single (j + 1)]
          · simp [weylShift]
          · intro k _ hk
            simp [weylShift, hk]
          · simp
        have hstep : finAddNat (j + 1) m = finAddNat j (m + 1) := by
          apply Fin.ext
          simp only [finAddNat, Fin.val_add, Fin.val_one', Nat.mod_add_mod, Nat.add_mod_mod]
          rw [add_assoc, add_comm 1 m]
        rw [heq, ihm i (j + 1), hstep]
  ext i j
  rw [hpow N i j]
  have hN : finAddNat j N = j := Fin.ext (by simp [finAddNat, Nat.mod_eq_of_lt j.isLt])
  rw [hN]
  simp [Matrix.one_apply]

theorem weylClockDag_pow_eq_one (N : ℕ) [NeZero N] : weylClockDag N ^ N = 1 := by
  ext i j
  unfold weylClockDag
  rw [Matrix.diagonal_pow, Matrix.diagonal_apply, Matrix.one_apply]
  by_cases hij : i = j
  · subst hij
    simp only [↓reduceIte, Pi.pow_apply]
    calc
      ((paraOmega N ^ (N - 1)) ^ i.val) ^ N
          = (paraOmega N ^ (N - 1)) ^ (i.val * N) := (pow_mul _ _ _).symm
      _ = ((paraOmega N ^ (N - 1)) ^ N) ^ i.val := by rw [mul_comm i.val N, pow_mul]
      _ = (paraOmega N ^ ((N - 1) * N)) ^ i.val := by rw [← pow_mul (paraOmega N) (N - 1) N]
      _ = ((paraOmega N ^ N) ^ (N - 1)) ^ i.val := by
            rw [mul_comm (N - 1) N, pow_mul (paraOmega N) N (N - 1)]
      _ = 1 := by rw [paraOmega_pow N, one_pow, one_pow]
  · simp [hij]

theorem weylShift_mul_weylClockDag (N : ℕ) (hN : 2 ≤ N) :
    haveI : NeZero N := ⟨Nat.ne_of_gt (lt_of_lt_of_le (by decide) hN)⟩
    weylShift N * weylClockDag N = paraOmega N • (weylClockDag N * weylShift N) := by
  have : NeZero N := ⟨Nat.ne_of_gt (lt_of_lt_of_le (by decide) hN)⟩
  have hinv : paraOmega N * paraOmega N ^ (N - 1) = 1 := by
    rw [← pow_succ', Nat.sub_add_cancel (le_trans (by decide) hN), paraOmega_pow N]
  ext i j
  simp only [Matrix.smul_apply, smul_eq_mul, Matrix.mul_apply, weylShift, weylClockDag,
    Matrix.diagonal_apply]
  rw [Finset.sum_eq_single j, Finset.sum_eq_single (j + 1)]
  · by_cases hij : i = j + 1
    · subst hij
      simp only [↓reduceIte, mul_one, one_mul]
      have hval : (j + 1 : Fin N).val = (j.val + 1) % N := by
        simp [Fin.val_add]
      by_cases hj : j.val + 1 < N
      · rw [hval, Nat.mod_eq_of_lt hj, pow_succ', ← mul_assoc, hinv, one_mul]
      · have hjN : j.val + 1 = N := by omega
        have hj_sub : j.val = N - 1 := by omega
        rw [hval, hjN, Nat.mod_self, pow_zero, mul_one, hj_sub]
        calc
          (paraOmega N ^ (N - 1)) ^ (N - 1) =
              1 * (paraOmega N ^ (N - 1)) ^ (N - 1) := (one_mul _).symm
          _ = (paraOmega N * paraOmega N ^ (N - 1)) *
                (paraOmega N ^ (N - 1)) ^ (N - 1) := by rw [hinv]
          _ = paraOmega N * (paraOmega N ^ (N - 1)) ^ N := by
              rw [mul_assoc, ← pow_succ']
              congr 2; omega
          _ = paraOmega N * 1 := by
              rw [← pow_mul, mul_comm (N - 1) N, pow_mul, paraOmega_pow N, one_pow]
          _ = paraOmega N := mul_one _
    · simp [hij]
  · intro k _ hk; simp [hk]
  · simp
  · intro k _ hk; simp [hk]
  · simp

/-- Kronecker embedding helpers on `Fin N × Fin N × Fin N`. -/
noncomputable def weylSite0 (N : ℕ) (A : Matrix (Fin N) (Fin N) ℂ) :
    Matrix (Fin N × Fin N × Fin N) (Fin N × Fin N × Fin N) ℂ :=
  fun p q => A p.1 q.1 * (if p.2.1 = q.2.1 ∧ p.2.2 = q.2.2 then 1 else 0)

noncomputable def weylSite1 (N : ℕ) (A B : Matrix (Fin N) (Fin N) ℂ) :
    Matrix (Fin N × Fin N × Fin N) (Fin N × Fin N × Fin N) ℂ :=
  fun p q => A p.1 q.1 * B p.2.1 q.2.1 * (if p.2.2 = q.2.2 then 1 else 0)

noncomputable def weylSite2 (N : ℕ) (A B C : Matrix (Fin N) (Fin N) ℂ) :
    Matrix (Fin N × Fin N × Fin N) (Fin N × Fin N × Fin N) ℂ :=
  fun p q => A p.1 q.1 * B p.2.1 q.2.1 * C p.2.2 q.2.2

private theorem weylSite2_mul (N : ℕ) (A₁ B₁ C₁ A₂ B₂ C₂ : Matrix (Fin N) (Fin N) ℂ) :
    weylSite2 N A₁ B₁ C₁ * weylSite2 N A₂ B₂ C₂ =
      weylSite2 N (A₁ * A₂) (B₁ * B₂) (C₁ * C₂) := by
  ext ⟨i₁, i₂, i₃⟩ ⟨j₁, j₂, j₃⟩
  simp only [weylSite2, Matrix.mul_apply, Fintype.sum_prod_type]
  calc
    ∑ k₁ : Fin N, ∑ k₂ : Fin N, ∑ k₃ : Fin N,
        (A₁ i₁ k₁ * B₁ i₂ k₂ * C₁ i₃ k₃) * (A₂ k₁ j₁ * B₂ k₂ j₂ * C₂ k₃ j₃) =
      ∑ k₁ : Fin N, ∑ k₂ : Fin N, ∑ k₃ : Fin N,
        (A₁ i₁ k₁ * A₂ k₁ j₁) * (B₁ i₂ k₂ * B₂ k₂ j₂) * (C₁ i₃ k₃ * C₂ k₃ j₃) := by
        refine Finset.sum_congr rfl fun k₁ _ =>
          Finset.sum_congr rfl fun k₂ _ =>
          Finset.sum_congr rfl fun k₃ _ => by ring
    _ = ∑ k₁ : Fin N, ∑ k₂ : Fin N,
          ((A₁ i₁ k₁ * A₂ k₁ j₁) * (B₁ i₂ k₂ * B₂ k₂ j₂)) *
            (∑ k₃ : Fin N, C₁ i₃ k₃ * C₂ k₃ j₃) := by
        refine Finset.sum_congr rfl fun k₁ _ => Finset.sum_congr rfl fun k₂ _ => ?_
        rw [← Finset.mul_sum]
    _ = ∑ k₁ : Fin N,
          ((A₁ i₁ k₁ * A₂ k₁ j₁) * ∑ k₂ : Fin N, B₁ i₂ k₂ * B₂ k₂ j₂) *
            (∑ k₃ : Fin N, C₁ i₃ k₃ * C₂ k₃ j₃) := by
        refine Finset.sum_congr rfl fun k₁ _ => ?_
        rw [← Finset.sum_mul, ← Finset.mul_sum]
    _ = (∑ k₁ : Fin N, A₁ i₁ k₁ * A₂ k₁ j₁) *
          (∑ k₂ : Fin N, B₁ i₂ k₂ * B₂ k₂ j₂) *
          (∑ k₃ : Fin N, C₁ i₃ k₃ * C₂ k₃ j₃) := by
        rw [← Finset.sum_mul, ← Finset.sum_mul]

private theorem weylSite2_pow (N : ℕ) (A B C : Matrix (Fin N) (Fin N) ℂ) (m : ℕ) :
    weylSite2 N A B C ^ m = weylSite2 N (A ^ m) (B ^ m) (C ^ m) := by
  induction m with
  | zero =>
      ext ⟨i₁, i₂, i₃⟩ ⟨j₁, j₂, j₃⟩
      simp [weylSite2, Matrix.one_apply, Prod.ext_iff]
      split_ifs <;> simp_all
  | succ m ihm =>
      rw [pow_succ, ihm, weylSite2_mul, pow_succ, pow_succ, pow_succ]

/-- Explicit 3-mode `N × N × N` Weyl matrix realization of `ParafermionSystem N 3`
for ALL `N ≥ 2`. -/
noncomputable def weylParafermionSystem (N : ℕ) (hN : 2 ≤ N) :
    ParafermionSystem N 3 ℂ
      (Matrix (Fin N × Fin N × Fin N) (Fin N × Fin N × Fin N) ℂ) :=
  letI : NeZero N := ⟨by omega⟩
  { omega := paraOmega N
    omega_pow := paraOmega_pow N
    omega_primitive := fun _ hk0 hkN => paraOmega_primitive N hN hk0 hkN
    psi := fun i =>
      if i = 0 then weylSite2 N (weylShift N) 1 1
      else if i = 1 then weylSite2 N (weylClockDag N) (weylShift N) 1
      else weylSite2 N (weylClockDag N) (weylClockDag N) (weylShift N)
    psi_pow := fun i => by
      fin_cases i
      · change weylSite2 N (weylShift N) 1 1 ^ N = 1
        rw [weylSite2_pow, weylShift_pow_eq_one, one_pow]
        ext ⟨a, b, c⟩ ⟨d, e, f⟩
        simp [weylSite2, Matrix.one_apply, Prod.ext_iff]
        split_ifs <;> simp_all
      · change weylSite2 N (weylClockDag N) (weylShift N) 1 ^ N = 1
        rw [weylSite2_pow, weylClockDag_pow_eq_one, weylShift_pow_eq_one, one_pow]
        ext ⟨a, b, c⟩ ⟨d, e, f⟩
        simp [weylSite2, Matrix.one_apply, Prod.ext_iff]
        split_ifs <;> simp_all
      · change weylSite2 N (weylClockDag N) (weylClockDag N) (weylShift N) ^ N = 1
        rw [weylSite2_pow, weylClockDag_pow_eq_one, weylShift_pow_eq_one]
        ext ⟨a, b, c⟩ ⟨d, e, f⟩
        simp [weylSite2, Matrix.one_apply, Prod.ext_iff]
        split_ifs <;> simp_all
    comm_phase := fun i j hij => by
      have hZX := weylShift_mul_weylClockDag N hN
      fin_cases i <;> fin_cases j <;> simp at hij ⊢
      · rw [weylSite2_mul, weylSite2_mul, hZX, ← Algebra.smul_def]
        ext ⟨a, b, c⟩ ⟨d, e, f⟩
        simp [weylSite2, Matrix.smul_apply, smul_eq_mul]; ring
      · rw [weylSite2_mul, weylSite2_mul, hZX, ← Algebra.smul_def]
        ext ⟨a, b, c⟩ ⟨d, e, f⟩
        simp [weylSite2, Matrix.smul_apply, smul_eq_mul]; ring
      · rw [weylSite2_mul, weylSite2_mul, hZX, ← Algebra.smul_def]
        ext ⟨a, b, c⟩ ⟨d, e, f⟩
        simp [weylSite2, Matrix.smul_apply, smul_eq_mul]; ring }

/-- Concrete `ParafermionSystem 3 3` witness realized by the Weyl clock/shift algebra. -/
noncomputable def weylParafermionSystem3 :
    ParafermionSystem 3 3 ℂ (Matrix (Fin 3 × Fin 3 × Fin 3) (Fin 3 × Fin 3 × Fin 3) ℂ) :=
  weylParafermionSystem 3 (by decide)

/-- Trace of `weylShift N ^ a * weylClockDag N ^ b` vanishes whenever `0 < a < N` or `0 < b < N`
(here specialized to nonzero off-diagonal shifts `weylShift N ^ a` for `0 < a < N`). -/
private theorem weylShift_pow_mul_diag_trace_zero {N : ℕ} (hN : 2 ≤ N)
    {k : ℕ} (hk0 : 0 < k) (hkN : k < N) (d : Fin N → ℂ) :
    haveI : NeZero N := ⟨Nat.ne_of_gt (lt_of_lt_of_le (by decide) hN)⟩
    Matrix.trace (weylShift N ^ k * Matrix.diagonal d) = 0 := by
  have : NeZero N := ⟨Nat.ne_of_gt (lt_of_lt_of_le (by decide) hN)⟩
  have hpow : ∀ (m : ℕ) (i j : Fin N),
      (weylShift N ^ m) i j = if i = finAddNat j m then 1 else 0 := by
    intro m
    induction m with
    | zero =>
        intro i j
        have hz : finAddNat j 0 = j := Fin.ext (by simp [finAddNat, Nat.mod_eq_of_lt j.isLt])
        rw [hz]
        simp [Matrix.one_apply]
    | succ m ihm =>
        intro i j
        rw [pow_succ, Matrix.mul_apply]
        have heq : (∑ l : Fin N, (weylShift N ^ m) i l * weylShift N l j) =
            (weylShift N ^ m) i (j + 1) := by
          rw [Finset.sum_eq_single (j + 1)]
          · simp [weylShift]
          · intro l _ hl; simp [weylShift, hl]
          · simp
        have hstep : finAddNat (j + 1) m = finAddNat j (m + 1) := by
          apply Fin.ext
          simp only [finAddNat, Fin.val_add, Fin.val_one', Nat.mod_add_mod, Nat.add_mod_mod]
          rw [add_assoc, add_comm 1 m]
        rw [heq, ihm i (j + 1), hstep]
  rw [Matrix.trace]
  refine Finset.sum_eq_zero fun i _ => ?_
  rw [Matrix.diag_apply, Matrix.mul_apply]
  refine Finset.sum_eq_zero fun j _ => ?_
  by_cases hij : i = j
  · subst hij
    rw [hpow k i i]
    have hne : i ≠ finAddNat i k := by
      intro heq
      have hval := congrArg Fin.val heq
      dsimp [finAddNat] at hval
      have hmod : (i.val + k) % N ≠ i.val := by
        by_cases hik : i.val + k < N
        · rw [Nat.mod_eq_of_lt hik]; exact Nat.ne_of_gt (Nat.lt_add_of_pos_right hk0)
        · have hge : N ≤ i.val + k := Nat.le_of_not_lt hik
          have hlt2 : i.val + k - N < N :=
            Nat.sub_lt_left_of_lt_add hge (Nat.add_lt_add i.isLt hkN)
          rw [Nat.mod_eq_sub_mod hge, Nat.mod_eq_of_lt hlt2]
          omega
      exact hmod hval.symm
    simp [hne]
  · simp [Ne.symm hij]

private theorem weylSite2_trace (N : ℕ) (A B C : Matrix (Fin N) (Fin N) ℂ) :
    Matrix.trace (weylSite2 N A B C) = Matrix.trace A * Matrix.trace B * Matrix.trace C := by
  simp only [Matrix.trace, Matrix.diag_apply, weylSite2, Fintype.sum_prod_type]
  calc
    ∑ i₁ : Fin N, ∑ i₂ : Fin N, ∑ i₃ : Fin N, A i₁ i₁ * B i₂ i₂ * C i₃ i₃ =
      ∑ i₁ : Fin N, ∑ i₂ : Fin N, (A i₁ i₁ * B i₂ i₂) * ∑ i₃ : Fin N, C i₃ i₃ := by
        refine Finset.sum_congr rfl fun i₁ _ => Finset.sum_congr rfl fun i₂ _ => ?_
        rw [← Finset.mul_sum]
    _ = ∑ i₁ : Fin N, (A i₁ i₁ * ∑ i₂ : Fin N, B i₂ i₂) * ∑ i₃ : Fin N, C i₃ i₃ := by
        refine Finset.sum_congr rfl fun i₁ _ => ?_
        rw [← Finset.sum_mul, ← Finset.mul_sum]
    _ = (∑ i₁ : Fin N, A i₁ i₁) * (∑ i₂ : Fin N, B i₂ i₂) * (∑ i₃ : Fin N, C i₃ i₃) := by
        rw [← Finset.sum_mul, ← Finset.sum_mul]

private theorem weylClockDag_pow_eq_diag (N : ℕ) [NeZero N] (m : ℕ) :
    weylClockDag N ^ m = Matrix.diagonal (fun i : Fin N => ((paraOmega N ^ (N - 1)) ^ i.val) ^ m) := by
  ext i j
  unfold weylClockDag
  rw [Matrix.diagonal_pow, Matrix.diagonal_apply, Matrix.diagonal_apply]
  rfl

private theorem weylShift_mul_diag_comm (N : ℕ) [NeZero N] (d : Fin N → ℂ) :
    ∃ d' : Fin N → ℂ, Matrix.diagonal d * weylShift N = weylShift N * Matrix.diagonal d' := by
  refine ⟨fun j => d (j + 1), ?_⟩
  ext i j
  simp only [Matrix.mul_apply, weylShift, Matrix.diagonal_apply]
  rw [Finset.sum_eq_single i, Finset.sum_eq_single j]
  · by_cases hij : i = j + 1
    · subst hij; simp
    · simp [hij]
  · intro k _ hk; simp [hk]
  · simp
  · intro k _ hk; simp [Ne.symm hk]
  · simp

private theorem weylShift_pow_mul_diag_comm (N : ℕ) [NeZero N] (m : ℕ) (d : Fin N → ℂ) :
    ∃ d' : Fin N → ℂ, Matrix.diagonal d * weylShift N ^ m = weylShift N ^ m * Matrix.diagonal d' := by
  induction m generalizing d with
  | zero => exact ⟨d, by simp⟩
  | succ m ihm =>
      obtain ⟨d1, hd1⟩ := weylShift_mul_diag_comm N d
      obtain ⟨d2, hd2⟩ := ihm d1
      refine ⟨d2, ?_⟩
      calc
        Matrix.diagonal d * weylShift N ^ (m + 1) =
            (Matrix.diagonal d * weylShift N) * weylShift N ^ m := by
          rw [pow_succ', mul_assoc]
        _ = (weylShift N * Matrix.diagonal d1) * weylShift N ^ m := by rw [hd1]
        _ = weylShift N * (Matrix.diagonal d1 * weylShift N ^ m) := mul_assoc _ _ _
        _ = weylShift N * (weylShift N ^ m * Matrix.diagonal d2) := by rw [hd2]
        _ = weylShift N ^ (m + 1) * Matrix.diagonal d2 := by rw [← mul_assoc, pow_succ']

private theorem weyl_word_trace_zero {N : ℕ} (hN : 2 ≤ N)
    (m₁ m₂ : ℕ) (k : ℕ) (hk0 : 0 < k) (hkN : k < N) :
    haveI : NeZero N := ⟨by omega⟩
    Matrix.trace (weylClockDag N ^ m₁ * weylShift N ^ k * weylClockDag N ^ m₂) = 0 := by
  have : NeZero N := ⟨by omega⟩
  obtain ⟨d', hd'⟩ := weylShift_pow_mul_diag_comm N k
    (fun i => ((paraOmega N ^ (N - 1)) ^ i.val) ^ m₁)
  rw [weylClockDag_pow_eq_diag N m₁, weylClockDag_pow_eq_diag N m₂, hd', mul_assoc,
    Matrix.diagonal_mul_diagonal]
  exact weylShift_pow_mul_diag_trace_zero hN hk0 hkN _

private theorem weyl_site_monomial_trace_zero_fst {N : ℕ} (hN : 2 ≤ N)
    {k : ℕ} (hk0 : 0 < k) (hkN : k < N)
    (d₁ d₂ : ℕ) (B C : Matrix (Fin N) (Fin N) ℂ) :
    haveI : NeZero N := ⟨by omega⟩
    Matrix.trace (weylSite2 N (weylClockDag N ^ d₁ * weylShift N ^ k * weylClockDag N ^ d₂) B C) = 0 := by
  rw [weylSite2_trace, weyl_word_trace_zero hN d₁ d₂ k hk0 hkN, zero_mul, zero_mul]

private theorem weyl_site_monomial_trace_zero_trd {N : ℕ} (hN : 2 ≤ N)
    {k : ℕ} (hk0 : 0 < k) (hkN : k < N)
    (d₁ d₂ : ℕ) (A B : Matrix (Fin N) (Fin N) ℂ) :
    haveI : NeZero N := ⟨by omega⟩
    Matrix.trace (weylSite2 N A B (weylClockDag N ^ d₁ * weylShift N ^ k * weylClockDag N ^ d₂)) = 0 := by
  rw [weylSite2_trace, weyl_word_trace_zero hN d₁ d₂ k hk0 hkN, mul_zero]

/-- **All-`N ≥ 3` Linear-Ansatz Braid Obstruction (Concrete Weyl Realization)**:
for EVERY `N ≥ 3`, ANY linear ansatz `R₁ = c₀ • 1 + c₁ • (ψ₀^{N-1} ψ₁)`,
`R₂ = c₀ • 1 + c₁ • (ψ₁^{N-1} ψ₂)` in `weylParafermionSystem N` fails the Artin braid
relation unless `c₀ = 0 ∨ c₁ = 0`. Proved cleanly via the grade-selecting trace
functional `M ↦ Tr((ψ₁^{N-1} ψ₀) * M)`. -/
theorem weyl_linear_ansatz_obstruction (N : ℕ) (hN : 3 ≤ N) (c₀ c₁ : ℂ) :
    let sys := weylParafermionSystem N (Nat.le_of_succ_le hN)
    let u₁ := sys.psi 0 ^ (N - 1) * sys.psi 1
    let u₂ := sys.psi 1 ^ (N - 1) * sys.psi 2
    (c₀ • 1 + c₁ • u₁) * (c₀ • 1 + c₁ • u₂) * (c₀ • 1 + c₁ • u₁) =
      (c₀ • 1 + c₁ • u₂) * (c₀ • 1 + c₁ • u₁) * (c₀ • 1 + c₁ • u₂) →
    c₀ = 0 ∨ c₁ = 0 := by
  intro sys u₁ u₂ hartin
  have : NeZero N := ⟨by omega⟩
  let u₁_inv := sys.psi 1 ^ (N - 1) * sys.psi 0
  let φ : Matrix (Fin N × Fin N × Fin N) (Fin N × Fin N × Fin N) ℂ →ₗ[ℂ] ℂ :=
    { toFun := fun M => Matrix.trace (u₁_inv * M)
      map_add' := fun A B => by simp [mul_add, Matrix.trace_add]
      map_smul' := fun r A => by simp [Algebra.mul_smul_comm, Matrix.trace_smul] }
  have h1_mul_inv : u₁_inv * u₁ = 1 := by
    dsimp [u₁_inv, u₁]
    calc
      sys.psi 1 ^ (N - 1) * sys.psi 0 * (sys.psi 0 ^ (N - 1) * sys.psi 1) =
          sys.psi 1 ^ (N - 1) * (sys.psi 0 * sys.psi 0 ^ (N - 1)) * sys.psi 1 := by
        simp only [mul_assoc]
      _ = sys.psi 1 ^ (N - 1) * 1 * sys.psi 1 := by
          rw [← pow_succ', Nat.sub_add_cancel (by omega), sys.psi_pow 0]
      _ = sys.psi 1 ^ N := by rw [mul_one, ← pow_succ, Nat.sub_add_cancel (by omega)]
      _ = 1 := sys.psi_pow 1
  have hφ₁ : φ u₁ ≠ 0 := by
    dsimp [φ]
    rw [h1_mul_inv, Matrix.trace_one, Fintype.card_prod, Fintype.card_prod, Fintype.card_fin]
    have hpos : 0 < N * (N * N) := by positivity
    exact Nat.cast_ne_zero.mpr hpos.ne'
  -- Helper reducing `weylSite2` powers/products cleanly:
  have hψ0_eq : sys.psi 0 = weylSite2 N (weylShift N) 1 1 := rfl
  have hψ1_eq : sys.psi 1 = weylSite2 N (weylClockDag N) (weylShift N) 1 := rfl
  have hψ2_eq : sys.psi 2 = weylSite2 N (weylClockDag N) (weylClockDag N) (weylShift N) := rfl
  have hu₁_inv_eq : u₁_inv =
      weylSite2 N (weylClockDag N ^ (N - 1) * weylShift N) (weylShift N ^ (N - 1)) 1 := by
    dsimp [u₁_inv]
    rw [hψ1_eq, hψ0_eq, weylSite2_pow, one_pow, weylSite2_mul, mul_one, mul_one]
  have hu₂_eq : u₂ =
      weylSite2 N (weylClockDag N ^ N) (weylShift N ^ (N - 1) * weylClockDag N) (weylShift N) := by
    dsimp [u₂]
    rw [hψ1_eq, hψ2_eq, weylSite2_pow, one_pow, weylSite2_mul, one_mul, ← pow_succ,
      Nat.sub_add_cancel (by omega)]
  have hu₁_eq : u₁ =
      weylSite2 N (weylShift N ^ (N - 1) * weylClockDag N) (weylShift N) 1 := by
    dsimp [u₁]
    rw [hψ0_eq, hψ1_eq, weylSite2_pow, one_pow, weylSite2_mul, one_mul, one_mul]
  have hφ₂ : φ u₂ = 0 := by
    dsimp [φ]
    rw [hu₁_inv_eq, hu₂_eq, weylSite2_mul, weylClockDag_pow_eq_one N, mul_one]
    have hword : weylClockDag N ^ (N - 1) * weylShift N =
        weylClockDag N ^ (N - 1) * weylShift N ^ 1 * weylClockDag N ^ 0 := by
      simp
    rw [hword]
    exact weyl_site_monomial_trace_zero_fst (by omega) (by decide) (by omega) _ _ _ _
  have hφ11 : φ (u₁ * u₁) = 0 := by
    dsimp [φ]
    -- `u₁_inv * (u₁ * u₁) = (u₁_inv * u₁) * u₁ = u₁`!
    rw [← mul_assoc, h1_mul_inv, one_mul, hu₁_eq]
    have hword : weylShift N ^ (N - 1) * weylClockDag N =
        weylClockDag N ^ 0 * weylShift N ^ (N - 1) * weylClockDag N ^ 1 := by simp
    rw [hword]
    exact weyl_site_monomial_trace_zero_fst (by omega) (by omega) (by omega) _ _ _ _
  have hφ22 : φ (u₂ * u₂) = 0 := by
    dsimp [φ]
    rw [hu₁_inv_eq, hu₂_eq, weylSite2_mul, weylSite2_mul, weylClockDag_pow_eq_one N, mul_one,
      mul_one]
    have hword : weylClockDag N ^ (N - 1) * weylShift N =
        weylClockDag N ^ (N - 1) * weylShift N ^ 1 * weylClockDag N ^ 0 := by simp
    rw [hword]
    exact weyl_site_monomial_trace_zero_fst (by omega) (by decide) (by omega) _ _ _ _
  have hφ121 : φ (u₁ * u₂ * u₁) = 0 := by
    dsimp [φ]
    -- `u₁_inv * (u₁ * u₂ * u₁) = u₂ * u₁`! Look: `(u₁_inv * u₁) * (u₂ * u₁) = u₂ * u₁`!
    calc
      Matrix.trace (u₁_inv * (u₁ * u₂ * u₁)) =
          Matrix.trace ((u₁_inv * u₁) * (u₂ * u₁)) := by simp only [mul_assoc]
      _ = Matrix.trace (u₂ * u₁) := by rw [h1_mul_inv, one_mul]
      _ = 0 := by
          rw [hu₂_eq, hu₁_eq, weylSite2_mul, mul_one, weylClockDag_pow_eq_one N, one_mul]
          have hword : weylShift N ^ (N - 1) * weylClockDag N =
              weylClockDag N ^ 0 * weylShift N ^ (N - 1) * weylClockDag N ^ 1 := by simp
          rw [hword]
          exact weyl_site_monomial_trace_zero_fst (by omega) (by omega) (by omega) _ _ _ _
  have hφ212 : φ (u₂ * u₁ * u₂) = 0 := by
    dsimp [φ]
    rw [hu₁_inv_eq, hu₂_eq, hu₁_eq, weylSite2_mul, weylSite2_mul, weylSite2_mul,
      one_mul, mul_one, weylClockDag_pow_eq_one N]
    have hword : weylShift N * weylShift N =
        weylClockDag N ^ 0 * weylShift N ^ 2 * weylClockDag N ^ 0 := by
      simp [pow_two]
    rw [hword]
    exact weyl_site_monomial_trace_zero_trd (by omega) (by omega) (by omega) _ _ _ _
  exact parafermion_linear_ansatz_obstruction sys u₁ u₂ c₀ c₁ φ
    hφ₁ hφ₂ hφ11 hφ22 hφ121 hφ212 hartin

/-- Concrete `N = 4` clock/shift covariance bridge to `FourthRootPeirceProjectors`. -/
theorem fourthRoot_clock_shift_parafermion_cov :
    FourthRootPeirceProjectors.degreeClock * FourthRootPeirceProjectors.cyclicShift =
      paraOmega 4 • (FourthRootPeirceProjectors.cyclicShift * FourthRootPeirceProjectors.degreeClock) := by
  have hom4 : paraOmega 4 = Complex.I := by
    unfold paraOmega
    rw [show (2 : ℂ) * Real.pi * Complex.I / (4 : ℕ) = (Real.pi / 2) * Complex.I by
      push_cast; ring]
    rw [Complex.exp_mul_I, Complex.cos_pi_div_two, Complex.sin_pi_div_two]
    simp
  rw [hom4]
  exact FourthRootPeirceProjectors.degreeClock_shift

/-- General helper: in any `ParafermionSystem 3 n K A`, adjacent pair operators
`u₁ = ψ_i^2 ψ_j` and `u₂ = ψ_j^2 ψ_k` (`i < j < k`) satisfy `u₁^3 = 1`, `u₂^3 = 1`,
and `u₁ * u₂ = ω • (u₂ * u₁)`. -/
theorem parafermion3_pair_cube {n : ℕ} {K A : Type*} [CommRing K] [Ring A] [Algebra K A]
    (sys : ParafermionSystem 3 n K A) {i j : Fin n} (hij : i < j) :
    (sys.psi i ^ 2 * sys.psi j) ^ 3 = 1 := by
  let a := sys.psi i
  let b := sys.psi j
  let ω := sys.omega
  have hω3 : ω ^ 3 = 1 := sys.omega_pow
  have ha3 : a * a * a = 1 := by simpa [pow_three, mul_assoc] using sys.psi_pow i
  have hb3 : b * b * b = 1 := by simpa [pow_three, mul_assoc] using sys.psi_pow j
  have hab : a * b = ω • (b * a) := by
    simpa only [Algebra.smul_def] using sys.comm_phase i j hij
  have hba : b * a = (ω ^ 2) • (a * b) := by
    calc
      b * a = (1 : K) • (b * a) := (one_smul _ _).symm
      _ = (ω ^ 3) • (b * a) := by rw [hω3]
      _ = (ω ^ 2) • (ω • (b * a)) := by rw [smul_smul, ← pow_succ]
      _ = (ω ^ 2) • (a * b) := by rw [hab]
  have hba2 : b * (a * a) = ω • ((a * a) * b) := by
    calc
      b * (a * a) = (b * a) * a := (mul_assoc _ _ _).symm
      _ = (ω ^ 2) • (a * b) * a := by rw [hba]
      _ = (ω ^ 2) • (a * (b * a)) := by rw [Algebra.smul_mul_assoc, mul_assoc]
      _ = (ω ^ 2) • (a * ((ω ^ 2) • (a * b))) := by rw [hba]
      _ = (ω ^ 3 * ω) • ((a * a) * b) := by
          rw [Algebra.mul_smul_comm, smul_smul, mul_assoc]
          congr 1; ring
      _ = ω • ((a * a) * b) := by rw [hω3, one_mul]
  have hb2a : (b * b) * a = ω • (a * (b * b)) := by
    calc
      (b * b) * a = b * (b * a) := mul_assoc _ _ _
      _ = b * ((ω ^ 2) • (a * b)) := by rw [hba]
      _ = (ω ^ 2) • ((b * a) * b) := by rw [Algebra.mul_smul_comm, mul_assoc]
      _ = (ω ^ 2) • ((ω ^ 2) • (a * b) * b) := by rw [hba]
      _ = (ω ^ 3 * ω) • (a * (b * b)) := by
          rw [Algebra.smul_mul_assoc, smul_smul, mul_assoc]
          congr 1; ring
      _ = ω • (a * (b * b)) := by rw [hω3, one_mul]
  have hb2a2 : (b * b) * (a * a) = (ω ^ 2) • ((a * a) * (b * b)) := by
    calc
      (b * b) * (a * a) = ((b * b) * a) * a := (mul_assoc _ _ _).symm
      _ = ω • (a * (b * b)) * a := by rw [hb2a]
      _ = ω • (a * ((b * b) * a)) := by rw [Algebra.smul_mul_assoc, mul_assoc]
      _ = ω • (a * (ω • (a * (b * b)))) := by rw [hb2a]
      _ = (ω ^ 2) • ((a * a) * (b * b)) := by
          rw [Algebra.mul_smul_comm, smul_smul, mul_assoc, ← sq]
  have hu2 : (a * a * b) * (a * a * b) = ω • (a * (b * b)) := by
    calc
      (a * a * b) * (a * a * b) = (a * a) * (b * (a * a)) * b := by
        simp only [mul_assoc]
      _ = (a * a) * (ω • ((a * a) * b)) * b := by rw [hba2]
      _ = ω • (((a * a * a) * a) * (b * b)) := by
        rw [Algebra.mul_smul_comm, Algebra.smul_mul_assoc]
        simp only [mul_assoc]
      _ = ω • (a * (b * b)) := by rw [ha3, one_mul]
  change (a ^ 2 * b) ^ 3 = 1
  rw [pow_three, pow_two, ← mul_assoc (a * a * b)]
  calc
    ((a * a * b) * (a * a * b)) * (a * a * b) =
        (ω • (a * (b * b))) * (a * a * b) := by rw [hu2]
    _ = ω • (a * ((b * b) * (a * a)) * b) := by
        rw [Algebra.smul_mul_assoc]; simp only [mul_assoc]
    _ = ω • (a * ((ω ^ 2) • ((a * a) * (b * b))) * b) := by rw [hb2a2]
    _ = (ω ^ 3) • ((a * a * a) * (b * b * b)) := by
        rw [Algebra.mul_smul_comm, Algebra.smul_mul_assoc, smul_smul, ← pow_succ']
        simp only [mul_assoc]
    _ = 1 := by rw [hω3, one_smul, ha3, hb3, mul_one]

/-- In any `ParafermionSystem 3 n K A`, adjacent pair operators `u₁ = ψ_i^2 ψ_j`
and `u₂ = ψ_j^2 ψ_k` (`i < j < k`) satisfy `u₁ * u₂ = ω • (u₂ * u₁)`. -/
theorem parafermion3_pair_comm {n : ℕ} {K A : Type*} [CommRing K] [Ring A] [Algebra K A]
    (sys : ParafermionSystem 3 n K A) {i j k : Fin n} (hij : i < j) (hjk : j < k) :
    (sys.psi i ^ 2 * sys.psi j) * (sys.psi j ^ 2 * sys.psi k) =
      sys.omega • ((sys.psi j ^ 2 * sys.psi k) * (sys.psi i ^ 2 * sys.psi j)) := by
  let a := sys.psi i
  let b := sys.psi j
  let c := sys.psi k
  let ω := sys.omega
  have hik : i < k := lt_trans hij hjk
  have hω3 : ω ^ 3 = 1 := sys.omega_pow
  have hb3 : b * b * b = 1 := by simpa [pow_three, mul_assoc] using sys.psi_pow j
  have hab : a * b = ω • (b * a) := by
    simpa only [Algebra.smul_def] using sys.comm_phase i j hij
  have hac : a * c = ω • (c * a) := by
    simpa only [Algebra.smul_def] using sys.comm_phase i k hik
  have hbc : b * c = ω • (c * b) := by
    simpa only [Algebra.smul_def] using sys.comm_phase j k hjk
  have hba : b * a = (ω ^ 2) • (a * b) := by
    calc
      b * a = (1 : K) • (b * a) := (one_smul _ _).symm
      _ = (ω ^ 3) • (b * a) := by rw [hω3]
      _ = (ω ^ 2) • (ω • (b * a)) := by rw [smul_smul, ← pow_succ]
      _ = (ω ^ 2) • (a * b) := by rw [hab]
  have hca : c * a = (ω ^ 2) • (a * c) := by
    calc
      c * a = (1 : K) • (c * a) := (one_smul _ _).symm
      _ = (ω ^ 3) • (c * a) := by rw [hω3]
      _ = (ω ^ 2) • (ω • (c * a)) := by rw [smul_smul, ← pow_succ]
      _ = (ω ^ 2) • (a * c) := by rw [hac]
  have hcb : c * b = (ω ^ 2) • (b * c) := by
    calc
      c * b = (1 : K) • (c * b) := (one_smul _ _).symm
      _ = (ω ^ 3) • (c * b) := by rw [hω3]
      _ = (ω ^ 2) • (ω • (c * b)) := by rw [smul_smul, ← pow_succ]
      _ = (ω ^ 2) • (b * c) := by rw [hbc]
  have hca2 : c * (a * a) = ω • ((a * a) * c) := by
    calc
      c * (a * a) = (c * a) * a := (mul_assoc _ _ _).symm
      _ = (ω ^ 2) • (a * c) * a := by rw [hca]
      _ = (ω ^ 2) • (a * (c * a)) := by rw [Algebra.smul_mul_assoc, mul_assoc]
      _ = (ω ^ 2) • (a * ((ω ^ 2) • (a * c))) := by rw [hca]
      _ = (ω ^ 3 * ω) • ((a * a) * c) := by
          rw [Algebra.mul_smul_comm, smul_smul, mul_assoc]
          congr 1; ring
      _ = ω • ((a * a) * c) := by rw [hω3, one_mul]
  have hb2a : (b * b) * a = ω • (a * (b * b)) := by
    calc
      (b * b) * a = b * (b * a) := mul_assoc _ _ _
      _ = b * ((ω ^ 2) • (a * b)) := by rw [hba]
      _ = (ω ^ 2) • ((b * a) * b) := by rw [Algebra.mul_smul_comm, mul_assoc]
      _ = (ω ^ 2) • ((ω ^ 2) • (a * b) * b) := by rw [hba]
      _ = (ω ^ 3 * ω) • (a * (b * b)) := by
          rw [Algebra.smul_mul_assoc, smul_smul, mul_assoc]
          congr 1; ring
      _ = ω • (a * (b * b)) := by rw [hω3, one_mul]
  have hb2a2 : (b * b) * (a * a) = (ω ^ 2) • ((a * a) * (b * b)) := by
    calc
      (b * b) * (a * a) = ((b * b) * a) * a := (mul_assoc _ _ _).symm
      _ = ω • (a * (b * b)) * a := by rw [hb2a]
      _ = ω • (a * ((b * b) * a)) := by rw [Algebra.smul_mul_assoc, mul_assoc]
      _ = ω • (a * (ω • (a * (b * b)))) := by rw [hb2a]
      _ = (ω ^ 2) • ((a * a) * (b * b)) := by
          rw [Algebra.mul_smul_comm, smul_smul, mul_assoc, ← sq]
  have hLHS : (a ^ 2 * b) * (b ^ 2 * c) = (a * a) * c := by
    rw [pow_two, pow_two]
    calc
      (a * a * b) * (b * b * c) = (a * a) * (b * b * b) * c := by simp only [mul_assoc]
      _ = (a * a) * c := by rw [hb3, mul_one]
  have hRHS : (b ^ 2 * c) * (a ^ 2 * b) = (ω ^ 2) • ((a * a) * c) := by
    rw [pow_two, pow_two]
    calc
      (b * b * c) * (a * a * b) = (b * b) * (c * (a * a)) * b := by simp only [mul_assoc]
      _ = (b * b) * (ω • ((a * a) * c)) * b := by rw [hca2]
      _ = ω • (((b * b) * (a * a)) * (c * b)) := by
          rw [Algebra.mul_smul_comm, Algebra.smul_mul_assoc]; simp only [mul_assoc]
      _ = ω • (((ω ^ 2) • ((a * a) * (b * b))) * ((ω ^ 2) • (b * c))) := by
          rw [hb2a2, hcb]
      _ = (ω * ω ^ 2 * ω ^ 2) • ((a * a) * (b * b * b) * c) := by
          rw [Algebra.smul_mul_assoc, Algebra.mul_smul_comm, smul_smul, smul_smul]
          simp only [mul_assoc]
      _ = (ω ^ 2) • ((a * a) * c) := by
          have hpow5 : ω * ω ^ 2 * ω ^ 2 = ω ^ 2 := by
            calc
              ω * ω ^ 2 * ω ^ 2 = ω ^ 3 * ω ^ 2 := by ring
              _ = ω ^ 2 := by rw [hω3, one_mul]
          rw [hb3, mul_one, hpow5]
  rw [hLHS, hRHS, smul_smul, ← pow_succ', hω3, one_smul]

/-- Concrete `N = 3` Weyl quadratic braid satisfying `R₁ * R₂ * R₁ = R₂ * R₁ * R₂`,
together with the `3 × 3` Burau representation from `Topology.Parafermion`. -/
theorem weyl3_quadratic_artin_and_burau (t : ℂ) :
    let sys := weylParafermionSystem 3 (by decide)
    let u₁ := sys.psi 0 ^ 2 * sys.psi 1
    let u₂ := sys.psi 1 ^ 2 * sys.psi 2
    ((1 + sys.omega • u₁ + sys.omega • (u₁ * u₁)) *
      (1 + sys.omega • u₂ + sys.omega • (u₂ * u₂)) *
      (1 + sys.omega • u₁ + sys.omega • (u₁ * u₁)) =
    (1 + sys.omega • u₂ + sys.omega • (u₂ * u₂)) *
      (1 + sys.omega • u₁ + sys.omega • (u₁ * u₁)) *
      (1 + sys.omega • u₂ + sys.omega • (u₂ * u₂))) ∧
    (Topology.Parafermion.sigma_1 t * Topology.Parafermion.sigma_2 t *
        Topology.Parafermion.sigma_1 t =
      Topology.Parafermion.sigma_2 t * Topology.Parafermion.sigma_1 t *
        Topology.Parafermion.sigma_2 t) := by
  refine ⟨?_, Topology.Parafermion.su3_parafermion_braiding t⟩
  exact quadraticZ3ArtinRelation (weylParafermionSystem 3 (by decide)).omega_pow
    (parafermion3_pair_cube (weylParafermionSystem 3 (by decide)) (by decide))
    (parafermion3_pair_cube (weylParafermionSystem 3 (by decide)) (by decide))
    (parafermion3_pair_comm (weylParafermionSystem 3 (by decide)) (by decide) (by decide))

private noncomputable def infParaPhase (N : ℕ) [NeZero N] (i : ℕ) (x : ℕ →₀ Fin N) : ℂ :=
  (paraOmega N ^ (N - 1)) ^ (∑ j ∈ x.support.filter (fun j => j < i), (x j).val)

private noncomputable def infParaPsi (N : ℕ) [NeZero N] (_hN : 2 ≤ N) (i : ℕ) :
    Module.End ℂ ((ℕ →₀ Fin N) →₀ ℂ) :=
  Finsupp.lsum ℂ fun x : ℕ →₀ Fin N =>
    LinearMap.id.smulRight (infParaPhase N i x • Finsupp.single (x + Finsupp.single i 1) (1 : ℂ))

private theorem infParaPsi_single (N : ℕ) [NeZero N] (hN : 2 ≤ N) (i : ℕ) (x : ℕ →₀ Fin N) :
    infParaPsi N hN i (Finsupp.single x (1 : ℂ)) =
      infParaPhase N i x • Finsupp.single (x + Finsupp.single i 1) (1 : ℂ) := by
  simp [infParaPsi]

private theorem infParaPhase_add_single_self (N : ℕ) [NeZero N] (i : ℕ) (x : ℕ →₀ Fin N)
    (c : Fin N) :
    infParaPhase N i (x + Finsupp.single i c) = infParaPhase N i x := by
  dsimp [infParaPhase]
  have hfilt : (x + Finsupp.single i c).support.filter (fun j => j < i) =
      x.support.filter (fun j => j < i) := by
    ext j
    simp only [Finset.mem_filter, Finsupp.mem_support_iff, Finsupp.add_apply, Finsupp.single_apply]
    constructor <;> rintro ⟨hj, hji⟩ <;> refine ⟨?_, hji⟩
    · have hne : i ≠ j := Nat.ne_of_gt hji
      rw [ite_eq_right_iff.mpr (fun h => absurd h hne), add_zero] at hj
      exact hj
    · have hne : i ≠ j := Nat.ne_of_gt hji
      rw [ite_eq_right_iff.mpr (fun h => absurd h hne), add_zero]
      exact hj
  rw [hfilt]
  congr 1
  refine Finset.sum_congr rfl fun j hj => ?_
  have hne : i ≠ j := Nat.ne_of_gt (Finset.mem_filter.mp hj).2
  rw [Finsupp.single_apply, ite_eq_right_iff.mpr (fun h => absurd h hne), add_zero]

private theorem infParaPhase_add_single_gt {N : ℕ} [NeZero N] (hN : 2 ≤ N) {i k : ℕ} (hik : i < k)
    (x : ℕ →₀ Fin N) :
    paraOmega N * infParaPhase N k (x + Finsupp.single i 1) = infParaPhase N k x := by
  have hinv : paraOmega N * paraOmega N ^ (N - 1) = 1 := by
    rw [← pow_succ', Nat.sub_add_cancel (le_trans (by decide) hN), paraOmega_pow N]
  have hmod : (paraOmega N ^ (N - 1)) ^ ((x i + 1 : Fin N).val) * paraOmega N =
      (paraOmega N ^ (N - 1)) ^ (x i).val := by
    have hval : (x i + 1 : Fin N).val = ((x i).val + 1) % N := by
      simp [Fin.val_add]
    by_cases hx : (x i).val + 1 < N
    · rw [hval, Nat.mod_eq_of_lt hx, pow_succ, mul_assoc,
        mul_comm (paraOmega N ^ (N - 1)) (paraOmega N), hinv, mul_one]
    · have hxN : (x i).val + 1 = N := by have := (x i).isLt; omega
      have hxi_sub : (x i).val = N - 1 := by omega
      rw [hval, hxN, Nat.mod_self, pow_zero, one_mul, hxi_sub]
      calc
        paraOmega N = paraOmega N * 1 := (mul_one _).symm
        _ = paraOmega N * ((paraOmega N ^ (N - 1)) ^ N) := by
            rw [← pow_mul, mul_comm (N - 1) N, pow_mul, paraOmega_pow N, one_pow]
        _ = (paraOmega N * paraOmega N ^ (N - 1)) * (paraOmega N ^ (N - 1)) ^ (N - 1) := by
            rw [mul_assoc, ← pow_succ']
            congr 2; omega
        _ = (paraOmega N ^ (N - 1)) ^ (N - 1) := by rw [hinv, one_mul]
  dsimp [infParaPhase]
  let S₀ := (x.support.filter (fun j => j < k)).erase i
  have hS_x : ∑ j ∈ x.support.filter (fun j => j < k), (x j).val =
      (x i).val + ∑ j ∈ S₀, (x j).val := by
    by_cases hi : i ∈ x.support.filter (fun j => j < k)
    · rw [← Finset.add_sum_erase _ _ hi]
    · have hxi0 : x i = 0 := by
        by_contra hne
        exact hi (Finset.mem_filter.mpr ⟨Finsupp.mem_support_iff.mpr hne, hik⟩)
      rw [hxi0, Fin.val_zero, zero_add]
      dsimp only [S₀]
      rw [Finset.erase_eq_of_notMem hi]
  have hS_x1 : ∑ j ∈ (x + Finsupp.single i (1 : Fin N)).support.filter (fun j => j < k),
      ((x + Finsupp.single i (1 : Fin N)) j).val =
      (x i + 1 : Fin N).val + ∑ j ∈ S₀, (x j).val := by
    by_cases h0 : (x i + 1 : Fin N) = 0
    · have hfilt : (x + Finsupp.single i (1 : Fin N)).support.filter (fun j => j < k) = S₀ := by
        ext j
        simp only [Finset.mem_filter, Finsupp.mem_support_iff, Finsupp.add_apply,
          Finsupp.single_apply, S₀, Finset.mem_erase]
        by_cases hji : j = i
        · subst hji; simp [h0]
        · have hij : i ≠ j := Ne.symm hji
          rw [ite_eq_right_iff.mpr (fun h => absurd h hij), add_zero]
          exact ⟨fun ⟨hxj, hjk⟩ => ⟨hji, hxj, hjk⟩, fun ⟨_, hxj, hjk⟩ => ⟨hxj, hjk⟩⟩
      rw [hfilt, h0, Fin.val_zero, zero_add]
      refine Finset.sum_congr rfl fun j hj => ?_
      have hji : j ≠ i := (Finset.mem_erase.mp hj).1
      rw [Finsupp.add_apply, Finsupp.single_apply,
        ite_eq_right_iff.mpr (fun h => absurd h.symm hji), add_zero]
    · have hfilt : (x + Finsupp.single i (1 : Fin N)).support.filter (fun j => j < k) = insert i S₀ := by
        ext j
        simp only [Finset.mem_filter, Finsupp.mem_support_iff, Finsupp.add_apply,
          Finsupp.single_apply, Finset.mem_insert, S₀, Finset.mem_erase]
        by_cases hji : j = i
        · subst hji; simp [h0, hik]
        · have hij : i ≠ j := Ne.symm hji
          rw [ite_eq_right_iff.mpr (fun h => absurd h hij), add_zero]
          exact ⟨fun ⟨hxj, hjk⟩ => Or.inr ⟨hji, hxj, hjk⟩,
            fun h => h.elim (fun he => absurd he hji) (fun ⟨_, hxj, hjk⟩ => ⟨hxj, hjk⟩)⟩
      rw [hfilt, Finset.sum_insert (Finset.notMem_erase i _), Finsupp.add_apply,
        Finsupp.single_apply]
      simp only [↓reduceIte]
      congr 1
      refine Finset.sum_congr rfl fun j hj => ?_
      have hji : j ≠ i := (Finset.mem_erase.mp hj).1
      rw [Finsupp.add_apply, Finsupp.single_apply,
        ite_eq_right_iff.mpr (fun h => absurd h.symm hji), add_zero]
  simp only [Finsupp.add_apply] at hS_x1
  rw [hS_x, hS_x1, pow_add, pow_add]
  calc
    paraOmega N * ((paraOmega N ^ (N - 1)) ^ (x i + 1 : Fin N).val *
        (paraOmega N ^ (N - 1)) ^ ∑ j ∈ S₀, (x j).val) =
      ((paraOmega N ^ (N - 1)) ^ (x i + 1 : Fin N).val * paraOmega N) *
        (paraOmega N ^ (N - 1)) ^ ∑ j ∈ S₀, (x j).val := by ring
    _ = (paraOmega N ^ (N - 1)) ^ (x i).val *
        (paraOmega N ^ (N - 1)) ^ ∑ j ∈ S₀, (x j).val := by rw [hmod]

/-- Infinite-mode Fock realization of `ParafermionSystem N n ℂ` (for ANY `N ≥ 2` and `n : ℕ`)
together with a genuine non-degenerate `ParafermionBraidData 3 n` via `quadraticZ3ArtinRelation`! -/
noncomputable def infParafermionSystem (N n : ℕ) [NeZero N] (hN : 2 ≤ N) :
    ParafermionSystem N n ℂ (Module.End ℂ ((ℕ →₀ Fin N) →₀ ℂ)) where
  omega := paraOmega N
  omega_pow := paraOmega_pow N
  omega_primitive _ hk0 hkN := paraOmega_primitive N hN hk0 hkN
  psi i := infParaPsi N hN i.val
  psi_pow i := by
    have hpow : ∀ m : ℕ, ∀ x : ℕ →₀ Fin N,
        (infParaPsi N hN i.val ^ m) (Finsupp.single x (1 : ℂ)) =
          (infParaPhase N i.val x ^ m) •
            Finsupp.single (x + m • Finsupp.single i.val (1 : Fin N)) (1 : ℂ) := by
      intro m
      induction m with
      | zero => intro x; simp
      | succ m ihm =>
          intro x
          have hphase_eq : infParaPhase N i.val (x + m • Finsupp.single i.val (1 : Fin N)) =
              infParaPhase N i.val x := by
            rw [Finsupp.smul_single]
            exact infParaPhase_add_single_self N i.val x (m • (1 : Fin N))
          rw [pow_succ', Module.End.mul_apply, ihm x, map_smul, infParaPsi_single,
            hphase_eq, smul_smul, mul_comm _ (infParaPhase N i.val x), ← pow_succ',
            add_assoc, add_nsmul, one_nsmul]
    apply LinearMap.ext
    intro v
    refine Finsupp.induction_linear v (by simp)
      (fun a b ha hb => by simp only [map_add, Module.End.one_apply] at ha hb ⊢; rw [ha, hb]) ?_
    intro x r
    have h1 : Finsupp.single x r = r • Finsupp.single x (1 : ℂ) := by simp [Finsupp.smul_single]
    rw [h1, map_smul, map_smul, hpow N x]
    have hph : infParaPhase N i.val x ^ N = 1 := by
      dsimp [infParaPhase]
      let S := ∑ j ∈ x.support.filter (fun j => j < i.val), (x j).val
      calc
        ((paraOmega N ^ (N - 1)) ^ S) ^ N
            = (paraOmega N ^ (N - 1)) ^ (S * N) := (pow_mul _ _ _).symm
        _ = ((paraOmega N ^ (N - 1)) ^ N) ^ S := by rw [mul_comm S N, pow_mul]
        _ = (paraOmega N ^ ((N - 1) * N)) ^ S := by rw [← pow_mul (paraOmega N) (N - 1) N]
        _ = ((paraOmega N ^ N) ^ (N - 1)) ^ S := by
              rw [mul_comm (N - 1) N, pow_mul (paraOmega N) N (N - 1)]
        _ = 1 := by rw [paraOmega_pow N, one_pow, one_pow]
    have hnsmul_val : ∀ m : ℕ, (m • (1 : Fin N)).val = m % N := by
      intro m
      induction m with
      | zero => simp
      | succ m ih =>
          rw [add_nsmul, one_nsmul, Fin.val_add, ih, Fin.val_one', Nat.mod_add_mod,
            Nat.add_mod_mod]
    have hN0 : N • (1 : Fin N) = 0 := Fin.ext (by rw [hnsmul_val N, Nat.mod_self]; rfl)
    have hNshift : N • Finsupp.single i.val (1 : Fin N) = 0 := by
      ext j
      simp only [Finsupp.coe_smul, Pi.smul_apply, Finsupp.single_apply, Finsupp.coe_zero,
        Pi.zero_apply]
      split_ifs <;> simp [hN0]
    rw [hph, one_smul, hNshift, add_zero]
    rfl
  comm_phase i j hij := by
    have hlt : i.val < j.val := hij
    apply LinearMap.ext
    intro v
    refine Finsupp.induction_linear v (by simp)
      (fun a b ha hb => by simp only [Module.End.mul_apply, map_add] at ha hb ⊢; rw [ha, hb]) ?_
    intro x r
    have h1 : Finsupp.single x r = r • Finsupp.single x (1 : ℂ) := by simp [Finsupp.smul_single]
    rw [h1, map_smul, map_smul]
    simp only [Module.End.mul_apply]
    rw [infParaPsi_single, map_smul, infParaPsi_single,
      infParaPsi_single, map_smul, infParaPsi_single, smul_smul, smul_smul]
    have hphi : infParaPhase N i.val (x + Finsupp.single j.val 1) = infParaPhase N i.val x := by
      dsimp [infParaPhase]
      have hfilt : (x + Finsupp.single j.val 1).support.filter (fun k => k < i.val) =
          x.support.filter (fun k => k < i.val) := by
        ext k
        simp only [Finset.mem_filter, Finsupp.mem_support_iff, Finsupp.add_apply,
          Finsupp.single_apply]
        constructor <;> rintro ⟨hk, hki⟩ <;> refine ⟨?_, hki⟩
        · have hkj : j.val ≠ k := Nat.ne_of_gt (lt_trans hki hlt)
          rw [ite_eq_right_iff.mpr (fun h => absurd h hkj), add_zero] at hk; exact hk
        · have hkj : j.val ≠ k := Nat.ne_of_gt (lt_trans hki hlt)
          rw [ite_eq_right_iff.mpr (fun h => absurd h hkj), add_zero]; exact hk
      rw [hfilt]
      congr 1
      refine Finset.sum_congr rfl fun k hk => ?_
      have hkj : j.val ≠ k := Nat.ne_of_gt (lt_trans (Finset.mem_filter.mp hk).2 hlt)
      rw [Finsupp.single_apply, ite_eq_right_iff.mpr (fun h => absurd h hkj), add_zero]
    rw [hphi, add_right_comm x (Finsupp.single j.val 1) (Finsupp.single i.val 1)]
    have hphj := infParaPhase_add_single_gt hN hlt x
    rw [Module.algebraMap_end_apply, smul_smul, smul_smul, smul_smul]
    congr 1
    calc
      r * infParaPhase N j.val x * infParaPhase N i.val x =
          r * (infParaPhase N i.val x * (paraOmega N * infParaPhase N j.val (x + Finsupp.single i.val 1))) := by
        rw [hphj]; ring
      _ = r * paraOmega N * infParaPhase N i.val x * infParaPhase N j.val (x + Finsupp.single i.val 1) := by
        ring

/-- Certified infinite-mode `ParafermionBraidData 3 n` over `ℂ` built from the emergent
quadratic Artin relation `R_i = 1 + ω u_i + ω u_i^2` (`u_i = ψ_i^2 ψ_{i+1}`). -/
noncomputable def infParafermionBraid3 (n : ℕ) :
    ParafermionBraidData 3 n ℂ (Module.End ℂ ((ℕ →₀ Fin 3) →₀ ℂ))
      (infParafermionSystem 3 n (by decide)) where
  R i :=
    let u := infParaPsi 3 (by decide) i ^ 2 * infParaPsi 3 (by decide) (i + 1)
    1 + paraOmega 3 • u + paraOmega 3 • (u * u)
  adjacent_artin i := by
    let s3 : ParafermionSystem 3 (i + 3) ℂ (Module.End ℂ ((ℕ →₀ Fin 3) →₀ ℂ)) :=
      infParafermionSystem 3 (i + 3) (by decide)
    have hcube1 : (s3.psi ⟨i, by omega⟩ ^ 2 * s3.psi ⟨i + 1, by omega⟩) ^ 3 = 1 :=
      parafermion3_pair_cube s3 (by exact Fin.mk_lt_mk.mpr (by omega))
    have hcube2 : (s3.psi ⟨i + 1, by omega⟩ ^ 2 * s3.psi ⟨i + 2, by omega⟩) ^ 3 = 1 :=
      parafermion3_pair_cube s3 (by exact Fin.mk_lt_mk.mpr (by omega))
    have hcomm := parafermion3_pair_comm s3 (i := ⟨i, by omega⟩) (j := ⟨i + 1, by omega⟩)
      (k := ⟨i + 2, by omega⟩) (Fin.mk_lt_mk.mpr (by omega)) (Fin.mk_lt_mk.mpr (by omega))
    exact quadraticZ3ArtinRelation (paraOmega_pow 3) hcube1 hcube2 hcomm
  far_commute i j hij := by
    let s3 : ParafermionSystem 3 (j + 2) ℂ (Module.End ℂ ((ℕ →₀ Fin 3) →₀ ℂ)) :=
      infParafermionSystem 3 (j + 2) (by decide)
    let uᵢ := s3.psi ⟨i, by omega⟩ ^ 2 * s3.psi ⟨i + 1, by omega⟩
    let uⱼ := s3.psi ⟨j, by omega⟩ ^ 2 * s3.psi ⟨j + 1, by omega⟩
    have hcomm_each : ∀ a b : Fin (j + 2), a < b → s3.psi a * s3.psi b = paraOmega 3 • (s3.psi b * s3.psi a) := by
      intro a b hab
      have hcp := (infParafermionSystem 3 (j + 2) (by decide)).comm_phase a b hab
      change s3.psi a * s3.psi b = algebraMap ℂ _ (paraOmega 3) * (s3.psi b * s3.psi a) at hcp
      simpa only [Algebra.smul_def] using hcp
    have h0j : s3.psi ⟨i, by omega⟩ * s3.psi ⟨j, by omega⟩ =
        paraOmega 3 • (s3.psi ⟨j, by omega⟩ * s3.psi ⟨i, by omega⟩) :=
      hcomm_each _ _ (Fin.mk_lt_mk.mpr (by omega))
    have h0j1 : s3.psi ⟨i, by omega⟩ * s3.psi ⟨j + 1, by omega⟩ =
        paraOmega 3 • (s3.psi ⟨j + 1, by omega⟩ * s3.psi ⟨i, by omega⟩) :=
      hcomm_each _ _ (Fin.mk_lt_mk.mpr (by omega))
    have h1j : s3.psi ⟨i + 1, by omega⟩ * s3.psi ⟨j, by omega⟩ =
        paraOmega 3 • (s3.psi ⟨j, by omega⟩ * s3.psi ⟨i + 1, by omega⟩) :=
      hcomm_each _ _ (Fin.mk_lt_mk.mpr (by omega))
    have h1j1 : s3.psi ⟨i + 1, by omega⟩ * s3.psi ⟨j + 1, by omega⟩ =
        paraOmega 3 • (s3.psi ⟨j + 1, by omega⟩ * s3.psi ⟨i + 1, by omega⟩) :=
      hcomm_each _ _ (Fin.mk_lt_mk.mpr (by omega))
    have huij : uᵢ * uⱼ = uⱼ * uᵢ := by
      dsimp [uᵢ, uⱼ]
      rw [pow_two, pow_two]
      let a := s3.psi ⟨i, by omega⟩
      let b := s3.psi ⟨i + 1, by omega⟩
      let c := s3.psi ⟨j, by omega⟩
      let d := s3.psi ⟨j + 1, by omega⟩
      let ω := paraOmega 3
      have hω3 : ω ^ 3 = 1 := paraOmega_pow 3
      have haB : a * (c * c * d) = (c * c * d) * a := by
        calc
          a * (c * c * d) = (a * c) * c * d := by simp only [mul_assoc]
          _ = (ω • (c * a)) * c * d := by rw [h0j]
          _ = ω • (c * (a * c) * d) := by
              rw [Algebra.smul_mul_assoc, Algebra.smul_mul_assoc]; simp only [mul_assoc]
          _ = ω • (c * (ω • (c * a)) * d) := by rw [h0j]
          _ = (ω * ω) • (c * c * (a * d)) := by
              rw [Algebra.mul_smul_comm, Algebra.smul_mul_assoc, smul_smul]; simp only [mul_assoc]
          _ = (ω * ω) • (c * c * (ω • (d * a))) := by rw [h0j1]
          _ = (ω ^ 3) • ((c * c * d) * a) := by
              rw [Algebra.mul_smul_comm, smul_smul]; simp only [mul_assoc]; congr 1; ring
          _ = (c * c * d) * a := by rw [hω3, one_smul]
      have hbB : b * (c * c * d) = (c * c * d) * b := by
        calc
          b * (c * c * d) = (b * c) * c * d := by simp only [mul_assoc]
          _ = (ω • (c * b)) * c * d := by rw [h1j]
          _ = ω • (c * (b * c) * d) := by
              rw [Algebra.smul_mul_assoc, Algebra.smul_mul_assoc]; simp only [mul_assoc]
          _ = ω • (c * (ω • (c * b)) * d) := by rw [h1j]
          _ = (ω * ω) • (c * c * (b * d)) := by
              rw [Algebra.mul_smul_comm, Algebra.smul_mul_assoc, smul_smul]; simp only [mul_assoc]
          _ = (ω * ω) • (c * c * (ω • (d * b))) := by rw [h1j1]
          _ = (ω ^ 3) • ((c * c * d) * b) := by
              rw [Algebra.mul_smul_comm, smul_smul]; simp only [mul_assoc]; congr 1; ring
          _ = (c * c * d) * b := by rw [hω3, one_smul]
      calc
        (a * a * b) * (c * c * d) = a * (a * (b * (c * c * d))) := by simp only [mul_assoc]
        _ = a * (a * ((c * c * d) * b)) := by rw [hbB]
        _ = a * ((a * (c * c * d)) * b) := by rw [← mul_assoc a (c * c * d) b]
        _ = a * (((c * c * d) * a) * b) := by rw [haB]
        _ = (a * (c * c * d)) * (a * b) := by
            rw [mul_assoc (c * c * d) a b, ← mul_assoc a (c * c * d) (a * b)]
        _ = ((c * c * d) * a) * (a * b) := by rw [haB]
        _ = (c * c * d) * (a * a * b) := by rw [mul_assoc (c * c * d) a (a * b), ← mul_assoc a a b]
    change (1 + paraOmega 3 • uᵢ + paraOmega 3 • (uᵢ * uᵢ)) *
        (1 + paraOmega 3 • uⱼ + paraOmega 3 • (uⱼ * uⱼ)) =
      (1 + paraOmega 3 • uⱼ + paraOmega 3 • (uⱼ * uⱼ)) *
        (1 + paraOmega 3 • uᵢ + paraOmega 3 • (uᵢ * uᵢ))
    have h1 : uᵢ * (uᵢ * uⱼ) = uⱼ * (uᵢ * uᵢ) := by
      calc
        uᵢ * (uᵢ * uⱼ) = uᵢ * (uⱼ * uᵢ) := by rw [huij]
        _ = (uᵢ * uⱼ) * uᵢ := (mul_assoc _ _ _).symm
        _ = uⱼ * (uᵢ * uᵢ) := by rw [huij, mul_assoc]
    have h2 : uᵢ * (uⱼ * uⱼ) = uⱼ * (uⱼ * uᵢ) := by
      calc
        uᵢ * (uⱼ * uⱼ) = (uᵢ * uⱼ) * uⱼ := (mul_assoc _ _ _).symm
        _ = (uⱼ * uᵢ) * uⱼ := by rw [huij]
        _ = uⱼ * (uᵢ * uⱼ) := mul_assoc _ _ _
        _ = uⱼ * (uⱼ * uᵢ) := by rw [huij]
    have h3 : uᵢ * (uᵢ * (uⱼ * uⱼ)) = uⱼ * (uⱼ * (uᵢ * uᵢ)) := by
      calc
        uᵢ * (uᵢ * (uⱼ * uⱼ)) = uᵢ * (uⱼ * (uⱼ * uᵢ)) := by rw [h2]
        _ = (uᵢ * uⱼ) * (uⱼ * uᵢ) := (mul_assoc _ _ _).symm
        _ = (uⱼ * uᵢ) * (uⱼ * uᵢ) := by rw [huij]
        _ = uⱼ * (uᵢ * (uⱼ * uᵢ)) := mul_assoc _ _ _
        _ = uⱼ * ((uᵢ * uⱼ) * uᵢ) := by rw [← mul_assoc uᵢ uⱼ uᵢ]
        _ = uⱼ * (uⱼ * (uᵢ * uᵢ)) := by rw [huij, mul_assoc uⱼ uᵢ uᵢ]
    simp only [add_mul, mul_add, Algebra.smul_mul_assoc, Algebra.mul_smul_comm,
      one_mul, mul_one, mul_assoc]
    rw [h1, h3, h2, huij]
    module

end InfiniteAndWeylParafermions

end InfoGeometry.Algebra
