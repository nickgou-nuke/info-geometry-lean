/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.Core.PeirceCompressionDefect
import Mathlib.Analysis.Normed.Ring.Basic
import Mathlib.Analysis.SpecificLimits.Basic

/-!
# Connected compression through a fixed vacuum corner

An idempotent `p` fixed on both sides by a transfer `t` splits its connected
compressed products into two directed Peirce arrows and the intervening
excitation transfer. All products retain their noncommutative order.

The norm estimates use the excitation-compression norm. Convergence additionally
requires an explicit strict contraction. These results do not construct an OS
transfer operator, prove uniformity through a continuum limit, or establish a
Yang–Mills mass gap.
-/

namespace InfoGeometry.Core.PeirceTransferDynamics

open PeirceCompressionDefect Filter
open scoped Topology

section Ring

variable {R : Type*} [Ring R]

private theorem fixed_left_pow (p t : R) (h : p * t = p) (n : ℕ) :
    p * t ^ n = p := by
  induction n with
  | zero => simp
  | succ n ih => rw [pow_succ, ← mul_assoc, ih, h]

private theorem fixed_right_pow (p t : R) (h : t * p = p) (n : ℕ) :
    t ^ n * p = p := by
  induction n with
  | zero => simp
  | succ n ih => rw [pow_succ', mul_assoc, ih, h]

/-- Vacuum subtraction agrees with the excitation compression. -/
theorem excitation_compression_eq_sub (p t : R) (hp : p * p = p)
    (htp : t * p = p) (hpt : p * t = p) :
    (1 - p) * t * (1 - p) = t - p := by
  noncomm_ring [hp, htp, hpt]

private theorem pow_mul_annihilated (p t z : R)
    (hpt : p * t = p) (hpz : p * z = 0) (n : ℕ) :
    t ^ n * z = (t - p) ^ n * z := by
  induction n with
  | zero => simp
  | succ n ih =>
    have hz : p * (t ^ n * z) = 0 := by
      rw [← mul_assoc, fixed_left_pow p t hpt n, hpz]
    calc
      t ^ (n + 1) * z = t * (t ^ n * z) := by rw [pow_succ', mul_assoc]
      _ = t * ((t - p) ^ n * z) := by rw [ih]
      _ = (t - p) * ((t - p) ^ n * z) := by
        simp only [sub_mul, ← ih]
        rw [hz, sub_zero]
      _ = (t - p) ^ (n + 1) * z := by rw [pow_succ', mul_assoc]

/-- The connected compressed word factors through the excitation sector at
every discrete time, including zero. Neither observable is required to commute
with the cut, with the transfer, or with the other observable. -/
theorem compression_transfer_power_eq (p t a b : R) (hp : p * p = p)
    (htp : t * p = p) (hpt : p * t = p) (n : ℕ) :
    p * (a * t ^ n * b) * p - (p * a * p) * (p * b * p) =
      (p * a * (1 - p)) * ((1 - p) * t * (1 - p)) ^ n * ((1 - p) * b * p) := by
  have hpT := fixed_left_pow p t hpt n
  have hTp := fixed_right_pow p t htp n
  have hleft : (p * a * (1 - p)) * p = 0 := by noncomm_ring [hp]
  have hright : p * ((1 - p) * b * p) = 0 := by
    simp only [← mul_assoc, mul_sub, mul_one, hp, sub_self, zero_mul]
  have hcenter : p * (t ^ n * b) * p = p * b * p := by
    rw [← mul_assoc, hpT]
  have hbase := compression_mul_defect p a (t ^ n * b) hp
  rw [hcenter] at hbase
  have hinsert : t ^ n * ((1 - p) * b * p) = t ^ n * b * p - p * b * p := by
    rw [← mul_assoc, ← mul_assoc, mul_sub, mul_one, hTp, sub_mul, sub_mul]
  have hremove : (p * a * (1 - p)) * (p * b * p) = 0 := by
    rw [← mul_assoc, ← mul_assoc, hleft, zero_mul, zero_mul]
  calc
    p * (a * t ^ n * b) * p - (p * a * p) * (p * b * p) =
        (p * a * (1 - p)) * (t ^ n * b * p) := by
          simpa only [mul_assoc] using hbase
    _ = (p * a * (1 - p)) * (t ^ n * ((1 - p) * b * p)) := by
      rw [hinsert, mul_sub, hremove, sub_zero]
    _ = (p * a * (1 - p)) * ((t - p) ^ n * ((1 - p) * b * p)) := by
      rw [pow_mul_annihilated p t _ hpt hright n]
    _ = (p * a * (1 - p)) * ((1 - p) * t * (1 - p)) ^ n * ((1 - p) * b * p) := by
      rw [excitation_compression_eq_sub p t hp htp hpt, mul_assoc]

end Ring

section NormedRing

variable {R : Type*} [NormedRing R]

/-- The connected transfer is bounded by the directed corner norms and the
power of the excitation-compression norm. The zero-time case avoids assuming
`NormOneClass` for the ambient normed ring. -/
theorem norm_compression_transfer_power_le (p t a b : R) (hp : p * p = p)
    (htp : t * p = p) (hpt : p * t = p) (n : ℕ) :
    ‖p * (a * t ^ n * b) * p - (p * a * p) * (p * b * p)‖ ≤
      ‖p * a * (1 - p)‖ * ‖(1 - p) * t * (1 - p)‖ ^ n * ‖(1 - p) * b * p‖ := by
  rw [compression_transfer_power_eq p t a b hp htp hpt n]
  cases n with
  | zero => simpa only [pow_zero, mul_one] using
      norm_mul_le (p * a * (1 - p)) ((1 - p) * b * p)
  | succ n =>
    calc
      _ ≤ (‖p * a * (1 - p)‖ * ‖((1 - p) * t * (1 - p)) ^ (n + 1)‖) *
          ‖(1 - p) * b * p‖ :=
        (norm_mul_le _ _).trans
          (mul_le_mul_of_nonneg_right (norm_mul_le _ _) (norm_nonneg _))
      _ ≤ _ := mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left (norm_pow_le' _ (Nat.succ_pos n)) (norm_nonneg _))
        (norm_nonneg _)

/-- An explicit excitation bound gives a geometric majorant for the ordered
connected word. The estimate `hbound` is an input, not a consequence of pinching. -/
theorem norm_compression_transfer_power_le_of_bound (p t a b : R)
    (hp : p * p = p) (htp : t * p = p) (hpt : p * t = p)
    (r : ℝ) (hbound : ‖(1 - p) * t * (1 - p)‖ ≤ r) (n : ℕ) :
    ‖p * (a * t ^ n * b) * p - (p * a * p) * (p * b * p)‖ ≤
      ‖p * a * (1 - p)‖ * r ^ n * ‖(1 - p) * b * p‖ := by
  exact (norm_compression_transfer_power_le p t a b hp htp hpt n).trans
    (mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (norm_nonneg _) hbound n)
        (norm_nonneg _)) (norm_nonneg _))

/-- Strict contraction in the excitation sector implies norm clustering of
the connected compressed words. No continuum or infinite-volume limit is taken. -/
theorem compression_transfer_power_tendsto_zero (p t a b : R)
    (hp : p * p = p) (htp : t * p = p) (hpt : p * t = p)
    (hcontract : ‖(1 - p) * t * (1 - p)‖ < 1) :
    Tendsto (fun n : ℕ => p * (a * t ^ n * b) * p - (p * a * p) * (p * b * p))
      atTop (𝓝 0) := by
  apply tendsto_zero_iff_norm_tendsto_zero.mpr
  have hpow := tendsto_pow_atTop_nhds_zero_of_lt_one
    (norm_nonneg ((1 - p) * t * (1 - p))) hcontract
  have hmajorant : Tendsto
      (fun n : ℕ => ‖p * a * (1 - p)‖ * ‖(1 - p) * t * (1 - p)‖ ^ n *
        ‖(1 - p) * b * p‖) atTop (𝓝 0) := by
    simpa only [mul_zero, zero_mul] using
      (hpow.const_mul ‖p * a * (1 - p)‖).mul_const ‖(1 - p) * b * p‖
  exact squeeze_zero (fun _ => norm_nonneg _)
    (norm_compression_transfer_power_le p t a b hp htp hpt) hmajorant

end NormedRing

end InfoGeometry.Core.PeirceTransferDynamics
