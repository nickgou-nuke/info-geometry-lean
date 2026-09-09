import Mathlib.Data.Matrix.Basic
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
  ring

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

end InfoGeometry.Canonical.FourMajoranaPfaffianMatching
