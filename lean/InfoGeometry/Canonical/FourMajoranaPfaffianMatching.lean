/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import Mathlib.Data.Matrix.Basic
import InfoGeometry.Algebra.FiniteSpinAlgebra
import Mathlib.Tactic
import InfoGeometry.Volume.OrientedPfaffian

/-!
# Four-Majorana matching channels

The first non-block-diagonal Pfaffian carrier has three perfect-matchings:
`(12)(34)`, `(13)(24)`, and `(14)(23)`.  This is a finite algebraic
readout; no continuum or Gaussian-state claim is made here.
-/

noncomputable section

namespace InfoGeometry.Canonical.FourMajoranaPfaffianMatching

open Matrix
open InfoGeometry.Volume.OrientedPfaffian

variable {R : Type*} [CommRing R]

def skew4 (a12 a13 a14 a23 a24 a34 : R) : Matrix (Fin 4) (Fin 4) R :=
  !![0, a12, a13, a14;
    -a12, 0, a23, a24;
    -a13, -a23, 0, a34;
    -a14, -a24, -a34, 0]

def pairing12_34 (a12 a34 : R) : R := a12 * a34
def pairing13_24 (a13 a24 : R) : R := -(a13 * a24)
def pairing14_23 (a14 a23 : R) : R := a14 * a23

def pfaffian4 (a12 a13 a14 a23 a24 a34 : R) : R :=
  pairing12_34 a12 a34 + pairing13_24 a13 a24 + pairing14_23 a14 a23

@[simp] theorem pfaffian4_eq_three_pairings
    (a12 a13 a14 a23 a24 a34 : R) :
    pfaffian4 a12 a13 a14 a23 a24 a34 =
      a12 * a34 - a13 * a24 + a14 * a23 := by
  simp [pfaffian4, pairing12_34, pairing13_24, pairing14_23]
  abel

theorem skew4_transpose
    (a12 a13 a14 a23 a24 a34 : R) :
    (skew4 a12 a13 a14 a23 a24 a34).transpose =
      -(skew4 a12 a13 a14 a23 a24 a34) := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [skew4]

def matching12_34 : PerfectMatching 2 where
  partner := ![1, 0, 3, 2]
  involutive := by intro i; fin_cases i <;> rfl
  fixed_free := by intro i; fin_cases i <;> decide

def matching13_24 : PerfectMatching 2 where
  partner := ![2, 3, 0, 1]
  involutive := by intro i; fin_cases i <;> rfl
  fixed_free := by intro i; fin_cases i <;> decide

def matching14_23 : PerfectMatching 2 where
  partner := ![3, 2, 1, 0]
  involutive := by intro i; fin_cases i <;> rfl
  fixed_free := by intro i; fin_cases i <;> decide

theorem four_majorana_matching_packet
    (a12 a13 a14 a23 a24 a34 : ℝ) :
    (skew4 a12 a13 a14 a23 a24 a34).transpose =
        -(skew4 a12 a13 a14 a23 a24 a34) ∧
    pfaffian4 a12 a13 a14 a23 a24 a34 =
        a12 * a34 - a13 * a24 + a14 * a23 := by
  exact ⟨skew4_transpose _ _ _ _ _ _,
    pfaffian4_eq_three_pairings _ _ _ _ _ _⟩


@[simp] theorem matching12_34_sign : matching12_34.matchingSign = 1 := by
  have h : matching12_34.crossingNumber = 0 := by decide
  simp [PerfectMatching.matchingSign, h]

@[simp] theorem matching13_24_sign : matching13_24.matchingSign = -1 := by
  have h : matching13_24.crossingNumber = 1 := by decide
  simp [PerfectMatching.matchingSign, h]

@[simp] theorem matching14_23_sign : matching14_23.matchingSign = 1 := by
  have h : matching14_23.crossingNumber = 0 := by decide
  simp [PerfectMatching.matchingSign, h]

@[simp] theorem matching12_34_weight
    (a12 a13 a14 a23 a24 a34 : ℝ) :
    matching12_34.matchingWeight (skew4 a12 a13 a14 a23 a24 a34) = a12 * a34 := by
  have hL : matching12_34.leftEndpoints = ({0, 2} : Finset (Fin 4)) := by decide
  have hp0 : matching12_34.partner 0 = 1 := by rfl
  have hp2 : matching12_34.partner 2 = 3 := by rfl
  simp [PerfectMatching.matchingWeight, hL, skew4, hp0, hp2]

@[simp] theorem matching13_24_weight
    (a12 a13 a14 a23 a24 a34 : ℝ) :
    matching13_24.matchingWeight (skew4 a12 a13 a14 a23 a24 a34) = a13 * a24 := by
  have hL : matching13_24.leftEndpoints = ({0, 1} : Finset (Fin 4)) := by decide
  have hp0 : matching13_24.partner 0 = 2 := by rfl
  have hp1 : matching13_24.partner 1 = 3 := by rfl
  simp [PerfectMatching.matchingWeight, hL, skew4, hp0, hp1]

@[simp] theorem matching14_23_weight
    (a12 a13 a14 a23 a24 a34 : ℝ) :
    matching14_23.matchingWeight (skew4 a12 a13 a14 a23 a24 a34) = a14 * a23 := by
  have hL : matching14_23.leftEndpoints = ({0, 1} : Finset (Fin 4)) := by decide
  have hp0 : matching14_23.partner 0 = 3 := by rfl
  have hp1 : matching14_23.partner 1 = 2 := by rfl
  simp [PerfectMatching.matchingWeight, hL, skew4, hp0, hp1]

theorem concrete_matching_signed_weights
    (a12 a13 a14 a23 a24 a34 : ℝ) :
    matching12_34.matchingSign *
        matching12_34.matchingWeight (skew4 a12 a13 a14 a23 a24 a34) = a12 * a34 ∧
    matching13_24.matchingSign *
        matching13_24.matchingWeight (skew4 a12 a13 a14 a23 a24 a34) = -(a13 * a24) ∧
    matching14_23.matchingSign *
        matching14_23.matchingWeight (skew4 a12 a13 a14 a23 a24 a34) = a14 * a23 := by
  simp

set_option maxHeartbeats 16000000 in
theorem det_fin_four (M : Matrix (Fin 4) (Fin 4) R) :
    M.det =
      M 0 0 * M 1 1 * M 2 2 * M 3 3 - M 0 0 * M 1 1 * M 2 3 * M 3 2
      - M 0 0 * M 1 2 * M 2 1 * M 3 3 + M 0 0 * M 1 2 * M 2 3 * M 3 1
      + M 0 0 * M 1 3 * M 2 1 * M 3 2 - M 0 0 * M 1 3 * M 2 2 * M 3 1
      - M 0 1 * M 1 0 * M 2 2 * M 3 3 + M 0 1 * M 1 0 * M 2 3 * M 3 2
      + M 0 1 * M 1 2 * M 2 0 * M 3 3 - M 0 1 * M 1 2 * M 2 3 * M 3 0
      - M 0 1 * M 1 3 * M 2 0 * M 3 2 + M 0 1 * M 1 3 * M 2 2 * M 3 0
      + M 0 2 * M 1 0 * M 2 1 * M 3 3 - M 0 2 * M 1 0 * M 2 3 * M 3 1
      - M 0 2 * M 1 1 * M 2 0 * M 3 3 + M 0 2 * M 1 1 * M 2 3 * M 3 0
      + M 0 2 * M 1 3 * M 2 0 * M 3 1 - M 0 2 * M 1 3 * M 2 1 * M 3 0
      - M 0 3 * M 1 0 * M 2 1 * M 3 2 + M 0 3 * M 1 0 * M 2 2 * M 3 1
      + M 0 3 * M 1 1 * M 2 0 * M 3 2 - M 0 3 * M 1 1 * M 2 2 * M 3 0
      - M 0 3 * M 1 2 * M 2 0 * M 3 1 + M 0 3 * M 1 2 * M 2 1 * M 3 0 := by
  rw [det_succ_row_zero, Fin.sum_univ_four]
  simp only [det_fin_three, submatrix_apply,
    Fin.succ_zero_eq_one, Fin.succ_one_eq_two,
    show Fin.succ (2 : Fin 3) = (3 : Fin 4) from rfl,
    show (0 : Fin 4).succAbove (0 : Fin 3) = 1 from by decide,
    show (0 : Fin 4).succAbove (1 : Fin 3) = 2 from by decide,
    show (0 : Fin 4).succAbove (2 : Fin 3) = 3 from by decide,
    show (1 : Fin 4).succAbove (0 : Fin 3) = 0 from by decide,
    show (1 : Fin 4).succAbove (1 : Fin 3) = 2 from by decide,
    show (1 : Fin 4).succAbove (2 : Fin 3) = 3 from by decide,
    show (2 : Fin 4).succAbove (0 : Fin 3) = 0 from by decide,
    show (2 : Fin 4).succAbove (1 : Fin 3) = 1 from by decide,
    show (2 : Fin 4).succAbove (2 : Fin 3) = 3 from by decide,
    show (3 : Fin 4).succAbove (0 : Fin 3) = 0 from by decide,
    show (3 : Fin 4).succAbove (1 : Fin 3) = 1 from by decide,
    show (3 : Fin 4).succAbove (2 : Fin 3) = 2 from by decide,
    show (0 : Fin 4).val = 0 from rfl, show (1 : Fin 4).val = 1 from rfl,
    show (2 : Fin 4).val = 2 from rfl, show (3 : Fin 4).val = 3 from rfl]
  ring

set_option maxHeartbeats 16000000 in
theorem pfaffian4_sq_eq_det
    (a12 a13 a14 a23 a24 a34 : R) :
    (pfaffian4 a12 a13 a14 a23 a24 a34) ^ 2 =
      (skew4 a12 a13 a14 a23 a24 a34).det := by
  rw [det_fin_four]
  simp [skew4, pfaffian4, pairing12_34, pairing13_24, pairing14_23]
  ring

theorem det_skew4_eq_three_pairings_sq
    (a12 a13 a14 a23 a24 a34 : R) :
    (skew4 a12 a13 a14 a23 a24 a34).det =
      (a12 * a34 - a13 * a24 + a14 * a23) ^ 2 := by
  rw [← pfaffian4_sq_eq_det]
  simp [pfaffian4, pairing12_34, pairing13_24, pairing14_23]
  ring

theorem det_skew4_nonneg
    (a12 a13 a14 a23 a24 a34 : ℝ) :
    0 ≤ (skew4 a12 a13 a14 a23 a24 a34).det := by
  rw [det_skew4_eq_three_pairings_sq]
  positivity

theorem four_majorana_pfaffian_packet
    (a12 a13 a14 a23 a24 a34 : R) :
    (skew4 a12 a13 a14 a23 a24 a34).transpose = -(skew4 a12 a13 a14 a23 a24 a34) ∧
    pfaffian4 a12 a13 a14 a23 a24 a34 = a12 * a34 - a13 * a24 + a14 * a23 ∧
    (pfaffian4 a12 a13 a14 a23 a24 a34) ^ 2 = (skew4 a12 a13 a14 a23 a24 a34).det :=
  ⟨skew4_transpose _ _ _ _ _ _, pfaffian4_eq_three_pairings _ _ _ _ _ _,
   pfaffian4_sq_eq_det _ _ _ _ _ _⟩
end InfoGeometry.Canonical.FourMajoranaPfaffianMatching
