/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import Mathlib
import InfoGeometry.Topology.WittenJonesChernSimonsKnots
import InfoGeometry.Canonical.TemperleyLiebKauffmanYangBaxter

/-!
# Transport of the concrete Witten–Jones TL pair to Mathlib matrices

The bespoke nine-field `Mat3` carrier is related explicitly to the standard
matrix ring. This file transports its operations and TL laws rather than
adding algebra instances to the bespoke carrier. The result connects the
existing concrete Kauffman calculation to the generic TL theorem. It makes no
claim that the separate framing-anomaly identity implies Yang–Baxter.
-/

noncomputable section

namespace InfoGeometry.Topology.WittenJonesTemperleyLiebTransport

open InfoGeometry.Topology.WittenJonesKnots
open InfoGeometry.Canonical.TemperleyLiebKauffmanYangBaxter
open TemperleyLiebJonesBridge

abbrev NativeMat3 := Matrix (Fin 3) (Fin 3) ℂ

/-- Two matrix units witness that the native carrier is genuinely
noncommutative; the transport target is not a scalar proxy. -/
def matrixUnit01 : NativeMat3 :=
  !![0, 1, 0; 0, 0, 0; 0, 0, 0]

def matrixUnit10 : NativeMat3 :=
  !![0, 0, 0; 1, 0, 0; 0, 0, 0]

theorem nativeMat3_noncommutative_witness :
    matrixUnit01 * matrixUnit10 ≠ matrixUnit10 * matrixUnit01 := by
  intro h
  have h00 := congrArg (fun M : NativeMat3 => M 0 0) h
  simp [matrixUnit01, matrixUnit10, Matrix.mul_apply,
    Fin.sum_univ_succ] at h00

/-- Fieldwise map from the custom Witten–Jones carrier to standard matrices. -/
def toNative (X : Mat3 ℂ) : NativeMat3 :=
  !![X.m00, X.m01, X.m02;
    X.m10, X.m11, X.m12;
    X.m20, X.m21, X.m22]

/-- The inverse fieldwise map. -/
def fromNative (M : NativeMat3) : Mat3 ℂ :=
  ⟨M 0 0, M 0 1, M 0 2,
   M 1 0, M 1 1, M 1 2,
   M 2 0, M 2 1, M 2 2⟩

/-- The carrier map is a bijection; its algebraic laws are proved separately. -/
def carrierEquiv : Mat3 ℂ ≃ NativeMat3 where
  toFun := toNative
  invFun := fromNative
  left_inv X := by
    ext <;> rfl
  right_inv M := by
    ext i j
    fin_cases i <;> fin_cases j <;> rfl

@[simp] theorem toNative_injective : Function.Injective toNative :=
  carrierEquiv.injective

@[simp] theorem toNative_one : toNative Mat3.one = (1 : NativeMat3) := by
  ext i j
  fin_cases i <;> fin_cases j <;> rfl

@[simp] theorem toNative_add (X Y : Mat3 ℂ) :
    toNative (Mat3.add X Y) = toNative X + toNative Y := by
  ext i j
  fin_cases i <;> fin_cases j <;> rfl

@[simp] theorem toNative_sub (X Y : Mat3 ℂ) :
    toNative (Mat3.sub X Y) = toNative X - toNative Y := by
  ext i j
  fin_cases i <;> fin_cases j <;> rfl

@[simp] theorem toNative_smul (c : ℂ) (X : Mat3 ℂ) :
    toNative (Mat3.smul c X) = c • toNative X := by
  ext i j
  fin_cases i <;> fin_cases j <;> rfl

@[simp] theorem toNative_mul (X Y : Mat3 ℂ) :
    toNative (Mat3.mul X Y) = toNative X * toNative Y := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [toNative, Mat3.mul, Matrix.mul_apply, Fin.sum_univ_succ] <;> ring

/-- The concrete Witten–Jones generators transported to the standard matrix
ring satisfy the abstract Temperley–Lieb relations. -/
def concreteTLSystem (CS : ChernSimonsPhase ℂ) :
    TemperleyLiebSystem (unknotVacuumLoop CS) NativeMat3 where
  e1 := toNative (tlGenE1 (unknotVacuumLoop CS))
  e2 := toNative (tlGenE2 (unknotVacuumLoop CS))
  self_loop_1 := by
    calc
      toNative (tlGenE1 (unknotVacuumLoop CS)) *
          toNative (tlGenE1 (unknotVacuumLoop CS)) =
          toNative (Mat3.mul (tlGenE1 (unknotVacuumLoop CS))
            (tlGenE1 (unknotVacuumLoop CS))) := by rw [toNative_mul]
      _ = toNative (Mat3.smul (unknotVacuumLoop CS)
            (tlGenE1 (unknotVacuumLoop CS))) := by
          rw [tlGenE1_sq]
      _ = unknotVacuumLoop CS • toNative (tlGenE1 (unknotVacuumLoop CS)) := by
          rw [toNative_smul]
  self_loop_2 := by
    calc
      toNative (tlGenE2 (unknotVacuumLoop CS)) *
          toNative (tlGenE2 (unknotVacuumLoop CS)) =
          toNative (Mat3.mul (tlGenE2 (unknotVacuumLoop CS))
            (tlGenE2 (unknotVacuumLoop CS))) := by rw [toNative_mul]
      _ = toNative (Mat3.smul (unknotVacuumLoop CS)
            (tlGenE2 (unknotVacuumLoop CS))) := by
          rw [tlGenE2_sq]
      _ = unknotVacuumLoop CS • toNative (tlGenE2 (unknotVacuumLoop CS)) := by
          rw [toNative_smul]
  contraction_121 := by
    calc
      (toNative (tlGenE1 (unknotVacuumLoop CS)) *
          toNative (tlGenE2 (unknotVacuumLoop CS))) *
          toNative (tlGenE1 (unknotVacuumLoop CS)) =
          toNative (Mat3.mul (Mat3.mul (tlGenE1 (unknotVacuumLoop CS))
            (tlGenE2 (unknotVacuumLoop CS)))
            (tlGenE1 (unknotVacuumLoop CS))) := by rw [toNative_mul, toNative_mul]
      _ = toNative (tlGenE1 (unknotVacuumLoop CS)) := by
          rw [tlGen_jones_cubic_121]
  contraction_212 := by
    calc
      (toNative (tlGenE2 (unknotVacuumLoop CS)) *
          toNative (tlGenE1 (unknotVacuumLoop CS))) *
          toNative (tlGenE2 (unknotVacuumLoop CS)) =
          toNative (Mat3.mul (Mat3.mul (tlGenE2 (unknotVacuumLoop CS))
            (tlGenE1 (unknotVacuumLoop CS)))
            (tlGenE2 (unknotVacuumLoop CS))) := by rw [toNative_mul, toNative_mul]
      _ = toNative (tlGenE2 (unknotVacuumLoop CS)) := by
          rw [tlGen_jones_cubic_212]

/-- A fixed matrix entry witnesses `e₁ ≠ e₂` for every concrete system. -/
theorem concreteTLSystem_generator_difference_01 (CS : ChernSimonsPhase ℂ) :
    (concreteTLSystem CS).e1 0 1 - (concreteTLSystem CS).e2 0 1 = 1 := by
  simp [concreteTLSystem, toNative, tlGenE1, tlGenE2]

@[simp] theorem toNative_kauffmanBraidR1 (CS : ChernSimonsPhase ℂ) :
    toNative (kauffmanBraidR1 CS) =
      braid1 (concreteTLSystem CS) CS.A CS.A_inv := by
  simp [kauffmanBraidR1, braid1, concreteTLSystem]

@[simp] theorem toNative_kauffmanBraidR2 (CS : ChernSimonsPhase ℂ) :
    toNative (kauffmanBraidR2 CS) =
      braid2 (concreteTLSystem CS) CS.A CS.A_inv := by
  simp [kauffmanBraidR2, braid2, concreteTLSystem]

/-- The existing concrete Witten–Jones braid equation follows by transporting
the generic Temperley–Lieb theorem through the explicit matrix equivalence. -/
theorem kauffmanBraid_yang_baxter_from_generic
    (CS : ChernSimonsPhase ℂ) (h_inv : CS.A * CS.A_inv = 1) :
    Mat3.mul (Mat3.mul (kauffmanBraidR1 CS) (kauffmanBraidR2 CS))
        (kauffmanBraidR1 CS) =
      Mat3.mul (Mat3.mul (kauffmanBraidR2 CS) (kauffmanBraidR1 CS))
        (kauffmanBraidR2 CS) := by
  apply toNative_injective
  simp only [toNative_mul, toNative_kauffmanBraidR1,
    toNative_kauffmanBraidR2]
  apply yang_baxter_of_reciprocal_kauffman_parameters
    (concreteTLSystem CS) CS.A CS.A_inv h_inv
  dsimp [unknotVacuumLoop]
  ring

/-- In the concrete nondegenerate TL matrix model, the reciprocal Kauffman
normalization is necessary as well as sufficient for the local braid
relation. The two nonzero hypotheses exclude degenerate parameter choices. -/
theorem kauffmanBraid_yang_baxter_iff_reciprocal
    (CS : ChernSimonsPhase ℂ)
    (h_b : CS.A_inv ≠ 0)
    (h_norm : CS.A ^ 2 + CS.A_inv ^ 2 ≠ 0) :
    Mat3.mul (Mat3.mul (kauffmanBraidR1 CS) (kauffmanBraidR2 CS))
        (kauffmanBraidR1 CS) =
      Mat3.mul (Mat3.mul (kauffmanBraidR2 CS) (kauffmanBraidR1 CS))
        (kauffmanBraidR2 CS) ↔
      CS.A * CS.A_inv = 1 := by
  constructor
  · intro h_ybe
    let sys := concreteTLSystem CS
    have hdef := braid_defect_eq_scalar_mul_generator_difference
      sys CS.A CS.A_inv
    have h_ybe_native :
        braid1 sys CS.A CS.A_inv * braid2 sys CS.A CS.A_inv *
            braid1 sys CS.A CS.A_inv =
          braid2 sys CS.A CS.A_inv * braid1 sys CS.A CS.A_inv *
            braid2 sys CS.A CS.A_inv := by
      simpa [sys, toNative_mul] using congrArg toNative h_ybe
    have h_eq :
        braid1 sys CS.A CS.A_inv * braid2 sys CS.A CS.A_inv *
            braid1 sys CS.A CS.A_inv -
          braid2 sys CS.A CS.A_inv * braid1 sys CS.A CS.A_inv *
            braid2 sys CS.A CS.A_inv = 0 := by
      exact sub_eq_zero.mpr h_ybe_native
    rw [h_eq] at hdef
    have h_entry := congrArg (fun M : NativeMat3 => M 0 1) hdef
    have h_difference_entry : (sys.e1 - sys.e2) 0 1 = 1 := by
      simpa [sys] using concreteTLSystem_generator_difference_01 CS
    have h_coeff :
        CS.A ^ 2 * CS.A_inv +
          CS.A * CS.A_inv ^ 2 * unknotVacuumLoop CS +
          CS.A_inv ^ 3 = 0 := by
      simpa [Matrix.smul_apply, Matrix.sub_apply, h_difference_entry] using
        h_entry.symm
    have h_factor :
        CS.A ^ 2 * CS.A_inv +
            CS.A * CS.A_inv ^ 2 * unknotVacuumLoop CS +
            CS.A_inv ^ 3 =
          (CS.A_inv * (CS.A ^ 2 + CS.A_inv ^ 2)) *
            (1 - CS.A * CS.A_inv) := by
      dsimp [unknotVacuumLoop]
      ring
    rw [h_factor] at h_coeff
    rcases mul_eq_zero.mp h_coeff with h_left | h_right
    · rcases mul_eq_zero.mp h_left with h_b_zero | h_norm_zero
      · exact (h_b h_b_zero).elim
      · exact (h_norm h_norm_zero).elim
    · have h_eq_one : 1 - CS.A * CS.A_inv = 0 := h_right
      linear_combination -h_eq_one
  · intro h_inv
    exact kauffmanBraid_yang_baxter_from_generic CS h_inv

end InfoGeometry.Topology.WittenJonesTemperleyLiebTransport
