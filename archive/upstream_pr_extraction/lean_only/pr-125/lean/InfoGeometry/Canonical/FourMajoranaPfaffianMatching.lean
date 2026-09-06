import Mathlib.Data.Matrix.Basic
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.Tactic
import InfoGeometry.Volume.OrientedPfaffian

/-!
# Four-Majorana Pfaffian and the three perfect-match pairing channels

This file closes the first non-block-diagonal Pfaffian case beyond the existing
2x2 and block-diagonal owners.  A general real/commutative-ring 4x4
skew-symmetric matrix has six independent entries and Pfaffian

  a12*a34 - a13*a24 + a14*a23.

These are exactly the three signed pairing channels
(12)(34), (13)(24), and (14)(23).  The square of this signed pairing sum is
proved to be the matrix determinant.

The three channels are also instantiated as genuine values of the repository's
`Volume.OrientedPfaffian.PerfectMatching 2` type.  Their crossing signs are
proved to be `+,-,+`, and their weights on the concrete skew matrix are the
three Pfaffian monomials.

This is a finite algebraic theorem.  It does not assert a planar Kasteleyn
orientation theorem, a Grassmann Gaussian integral in arbitrary dimension, or
a Moore--Read wavefunction identity.
-/

noncomputable section

namespace InfoGeometry.Canonical.FourMajoranaPfaffianMatching

open Matrix
open InfoGeometry.Volume.OrientedPfaffian

variable {R : Type*} [CommRing R]

/-- General 4x4 skew-symmetric matrix, written in its six independent entries. -/
def skew4 (a12 a13 a14 a23 a24 a34 : R) : Matrix (Fin 4) (Fin 4) R :=
  !![0,     a12,  a13,  a14;
     -a12,  0,    a23,  a24;
     -a13, -a23,  0,    a34;
     -a14, -a24, -a34,  0]

/-- The three signed perfect-matching channels for four labels. -/
def pairing12_34 (a12 a34 : R) : R := a12 * a34

def pairing13_24 (a13 a24 : R) : R := -(a13 * a24)

def pairing14_23 (a14 a23 : R) : R := a14 * a23

/-- Four-Majorana Pfaffian as the signed sum over the three pairings. -/
def pfaffian4 (a12 a13 a14 a23 a24 a34 : R) : R :=
  pairing12_34 a12 a34 + pairing13_24 a13 a24 + pairing14_23 a14 a23

@[simp] theorem pfaffian4_eq_three_pairings
    (a12 a13 a14 a23 a24 a34 : R) :
    pfaffian4 a12 a13 a14 a23 a24 a34 =
      a12 * a34 - a13 * a24 + a14 * a23 := by
  simp [pfaffian4, pairing12_34, pairing13_24, pairing14_23]

/-- The displayed carrier is genuinely skew-symmetric. -/
theorem skew4_transpose
    (a12 a13 a14 a23 a24 a34 : R) :
    (skew4 a12 a13 a14 a23 a24 a34).transpose =
      -(skew4 a12 a13 a14 a23 a24 a34) := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [skew4]

/-! ## Concrete perfect matchings on four Majorana labels -/

/-- Pairing `(01)(23)`, corresponding to the conventional `(12)(34)` channel. -/
def matching12_34 : PerfectMatching 2 where
  partner := ![1, 0, 3, 2]
  involutive := by intro i; fin_cases i <;> rfl
  fixed_free := by intro i; fin_cases i <;> decide

/-- Pairing `(02)(13)`, the unique crossing channel. -/
def matching13_24 : PerfectMatching 2 where
  partner := ![2, 3, 0, 1]
  involutive := by intro i; fin_cases i <;> rfl
  fixed_free := by intro i; fin_cases i <;> decide

/-- Pairing `(03)(12)`, the nested non-crossing channel. -/
def matching14_23 : PerfectMatching 2 where
  partner := ![3, 2, 1, 0]
  involutive := by intro i; fin_cases i <;> rfl
  fixed_free := by intro i; fin_cases i <;> decide

@[simp] theorem matching12_34_sign : matching12_34.matchingSign = 1 := by
  norm_num [PerfectMatching.matchingSign, PerfectMatching.crossingNumber,
    PerfectMatching.crossingPairs, PerfectMatching.leftEndpoints, matching12_34]

@[simp] theorem matching13_24_sign : matching13_24.matchingSign = -1 := by
  norm_num [PerfectMatching.matchingSign, PerfectMatching.crossingNumber,
    PerfectMatching.crossingPairs, PerfectMatching.leftEndpoints, matching13_24]

@[simp] theorem matching14_23_sign : matching14_23.matchingSign = 1 := by
  norm_num [PerfectMatching.matchingSign, PerfectMatching.crossingNumber,
    PerfectMatching.crossingPairs, PerfectMatching.leftEndpoints, matching14_23]

@[simp] theorem matching12_34_weight
    (a12 a13 a14 a23 a24 a34 : ℝ) :
    matching12_34.matchingWeight (skew4 a12 a13 a14 a23 a24 a34) =
      a12 * a34 := by
  norm_num [PerfectMatching.matchingWeight, PerfectMatching.leftEndpoints,
    matching12_34, skew4]

@[simp] theorem matching13_24_weight
    (a12 a13 a14 a23 a24 a34 : ℝ) :
    matching13_24.matchingWeight (skew4 a12 a13 a14 a23 a24 a34) =
      a13 * a24 := by
  norm_num [PerfectMatching.matchingWeight, PerfectMatching.leftEndpoints,
    matching13_24, skew4]

@[simp] theorem matching14_23_weight
    (a12 a13 a14 a23 a24 a34 : ℝ) :
    matching14_23.matchingWeight (skew4 a12 a13 a14 a23 a24 a34) =
      a14 * a23 := by
  norm_num [PerfectMatching.matchingWeight, PerfectMatching.leftEndpoints,
    matching14_23, skew4]

/-- The three concrete matching contributions reproduce the signed Pfaffian
monomials `+a12*a34`, `-a13*a24`, `+a14*a23`. -/
theorem concrete_matching_signed_weights
    (a12 a13 a14 a23 a24 a34 : ℝ) :
    matching12_34.matchingSign *
        matching12_34.matchingWeight (skew4 a12 a13 a14 a23 a24 a34) =
          a12 * a34 ∧
    matching13_24.matchingSign *
        matching13_24.matchingWeight (skew4 a12 a13 a14 a23 a24 a34) =
          -(a13 * a24) ∧
    matching14_23.matchingSign *
        matching14_23.matchingWeight (skew4 a12 a13 a14 a23 a24 a34) =
          a14 * a23 := by
  simp

/-- Expansion of a 4x4 determinant into the standard 24-term formula.
This local lemma is reused from the repository's finite Vandermonde lane. -/
set_option maxHeartbeats 16000000 in
private theorem det_fin_four (M : Matrix (Fin 4) (Fin 4) R) :
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

/-- Cayley's identity in the first genuinely nontrivial matching case:
the signed three-pairing Pfaffian squares to the determinant. -/
set_option maxHeartbeats 16000000 in
theorem pfaffian4_sq_eq_det
    (a12 a13 a14 a23 a24 a34 : R) :
    (pfaffian4 a12 a13 a14 a23 a24 a34) ^ 2 =
      (skew4 a12 a13 a14 a23 a24 a34).det := by
  rw [det_fin_four]
  simp [skew4, pfaffian4, pairing12_34, pairing13_24, pairing14_23]
  ring

/-- Determinant readout entirely in the three matching channels. -/
theorem det_skew4_eq_three_pairings_sq
    (a12 a13 a14 a23 a24 a34 : R) :
    (skew4 a12 a13 a14 a23 a24 a34).det =
      (a12 * a34 - a13 * a24 + a14 * a23) ^ 2 := by
  rw [← pfaffian4_sq_eq_det]
  simp [pfaffian4, pairing12_34, pairing13_24, pairing14_23]

/-- The four-Majorana determinant is nonnegative over the reals. -/
theorem det_skew4_nonneg
    (a12 a13 a14 a23 a24 a34 : ℝ) :
    0 ≤ (skew4 a12 a13 a14 a23 a24 a34).det := by
  rw [det_skew4_eq_three_pairings_sq]
  positivity

/-- Compact packet exposing skew symmetry, the three matching channels, and
Pfaffian-square determinant closure. -/
theorem four_majorana_pfaffian_packet
    (a12 a13 a14 a23 a24 a34 : R) :
    (skew4 a12 a13 a14 a23 a24 a34).transpose =
        -(skew4 a12 a13 a14 a23 a24 a34) ∧
    pfaffian4 a12 a13 a14 a23 a24 a34 =
        a12 * a34 - a13 * a24 + a14 * a23 ∧
    (pfaffian4 a12 a13 a14 a23 a24 a34) ^ 2 =
        (skew4 a12 a13 a14 a23 a24 a34).det :=
  ⟨skew4_transpose _ _ _ _ _ _,
   pfaffian4_eq_three_pairings _ _ _ _ _ _,
   pfaffian4_sq_eq_det _ _ _ _ _ _⟩

end InfoGeometry.Canonical.FourMajoranaPfaffianMatching
