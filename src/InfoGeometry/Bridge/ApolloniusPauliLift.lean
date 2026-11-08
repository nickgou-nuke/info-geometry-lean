import Mathlib.Tactic
import InfoGeometry.Algebra.FiniteSpinAlgebra
import InfoGeometry.Coordinate.ApolloniusLogCoordinates
import InfoGeometry.Canonical.PauliHestenesSpinMomentum

/-!
# Apollonius Pauli lift

This file lifts the logarithmic Apollonius coordinates to the diagonal Cartan
subgroup of `SL(2, ℂ)`.  The spinorial action `X ↦ g X gᴴ` gives the exact
longitudinal light-cone weights `exp (±η)` and transverse circular weights
`exp (±iθ)`.

The finite element is written explicitly, so none of these statements relies
on an unproved matrix-exponential identification.
-/

noncomputable section

namespace InfoGeometry.PauliLift

open scoped Matrix
open InfoGeometry.Apollonius

abbrev Mat2C := InfoGeometry.Algebra.FiniteSpin.Mat2C

/-- Complex Cartan coordinate `η + iθ`. -/
def cartanCoordinate (s : PuncturedPlane) : ℂ :=
  (eta s : ℂ) + Complex.I * (theta s : ℂ)

/-- Logarithmic Cartan generator `K = (η + iθ) σ₃ / 2`. -/
def logGenerator (s : PuncturedPlane) : Mat2C :=
  (cartanCoordinate s / 2) •
    InfoGeometry.Canonical.PauliHestenesSpinMomentum.PauliParavector.sigma3

private def upperWeight (s : PuncturedPlane) : ℂ :=
  Complex.exp (cartanCoordinate s / 2)

private def lowerWeight (s : PuncturedPlane) : ℂ :=
  Complex.exp (-(cartanCoordinate s / 2))

/-- Finite diagonal Cartan element. -/
def groupElement (s : PuncturedPlane) : Mat2C :=
  !![upperWeight s, 0; 0, lowerWeight s]

@[simp]
theorem groupElement_det_one (s : PuncturedPlane) :
    Matrix.det (groupElement s) = 1 := by
  simp [groupElement, upperWeight, lowerWeight, Matrix.det_fin_two]
  rw [← Complex.exp_add]
  have hzero :
      cartanCoordinate s / 2 + -(cartanCoordinate s / 2) = 0 := by ring
  rw [hzero, Complex.exp_zero]

/-- Spinorial Lorentz action `X ↦ g X gᴴ`. -/
def lorentzAction (s : PuncturedPlane) (X : Mat2C) : Mat2C :=
  groupElement s * X * Matrix.conjTranspose (groupElement s)

private theorem upperWeight_mul_conj (s : PuncturedPlane) :
    upperWeight s * (starRingEnd ℂ) (upperWeight s) =
      (Real.exp (eta s) : ℂ) := by
  rw [upperWeight, ← Complex.exp_conj, ← Complex.exp_add]
  have hsum :
      cartanCoordinate s / 2 +
          (starRingEnd ℂ) (cartanCoordinate s / 2) =
        (eta s : ℂ) := by
    simp [Complex.star_def, cartanCoordinate]
    rw [show (starRingEnd ℂ) (2 : ℂ) = 2 by
      exact map_ofNat (starRingEnd ℂ) 2]
    ring
  rw [hsum]
  exact (Complex.ofReal_exp (eta s)).symm

private theorem lowerWeight_mul_conj (s : PuncturedPlane) :
    lowerWeight s * (starRingEnd ℂ) (lowerWeight s) =
      (Real.exp (-eta s) : ℂ) := by
  rw [lowerWeight, ← Complex.exp_conj, ← Complex.exp_add]
  have hsum :
      -(cartanCoordinate s / 2) +
          (starRingEnd ℂ) (-(cartanCoordinate s / 2)) =
        (-eta s : ℂ) := by
    simp [Complex.star_def, cartanCoordinate]
    rw [show (starRingEnd ℂ) (2 : ℂ) = 2 by
      exact map_ofNat (starRingEnd ℂ) 2]
    ring
  rw [hsum]
  convert (Complex.ofReal_exp (-eta s)).symm using 1 <;> norm_num

private theorem upperWeight_mul_conj_lower (s : PuncturedPlane) :
    upperWeight s * (starRingEnd ℂ) (lowerWeight s) =
      Complex.exp (Complex.I * (theta s : ℂ)) := by
  rw [upperWeight, lowerWeight, ← Complex.exp_conj, ← Complex.exp_add]
  congr 1
  simp [cartanCoordinate]
  rw [show (starRingEnd ℂ) (2 : ℂ) = 2 by
    exact map_ofNat (starRingEnd ℂ) 2]
  ring

private theorem lowerWeight_mul_conj_upper (s : PuncturedPlane) :
    lowerWeight s * (starRingEnd ℂ) (upperWeight s) =
      Complex.exp (-Complex.I * (theta s : ℂ)) := by
  rw [lowerWeight, upperWeight, ← Complex.exp_conj, ← Complex.exp_add]
  congr 1
  simp [cartanCoordinate]
  rw [show (starRingEnd ℂ) (2 : ℂ) = 2 by
    exact map_ofNat (starRingEnd ℂ) 2]
  ring

/-- The upper null component scales by `exp η`. -/
theorem lorentz_null_plus_scaling
    (s : PuncturedPlane) (Xplus : ℝ) :
    let X : Mat2C := !![(Xplus : ℂ), 0; 0, 0]
    (lorentzAction s X) 0 0 =
      ((Real.exp (eta s) * Xplus : ℝ) : ℂ) := by
  dsimp [lorentzAction, groupElement]
  simp [Matrix.mul_apply, Matrix.conjTranspose, Fin.sum_univ_two,
    upperWeight_mul_conj]
  rw [mul_assoc]
  calc
    upperWeight s * (↑Xplus * (starRingEnd ℂ) (upperWeight s)) =
        ↑Xplus * (upperWeight s * (starRingEnd ℂ) (upperWeight s)) := by ring
    _ = ↑Xplus * (Real.exp (eta s) : ℂ) := by rw [upperWeight_mul_conj]
    _ = Complex.exp (eta s) * (Xplus : ℂ) := by
      rw [Complex.ofReal_exp]
      ring

/-- The lower null component scales by `exp (-η)`. -/
theorem lorentz_null_minus_scaling
    (s : PuncturedPlane) (Xminus : ℝ) :
    let X : Mat2C := !![0, 0; 0, (Xminus : ℂ)]
    (lorentzAction s X) 1 1 =
      ((Real.exp (-eta s) * Xminus : ℝ) : ℂ) := by
  dsimp [lorentzAction, groupElement]
  simp [Matrix.mul_apply, Matrix.conjTranspose, Fin.sum_univ_two,
    lowerWeight_mul_conj]
  rw [mul_assoc]
  calc
    lowerWeight s * (↑Xminus * (starRingEnd ℂ) (lowerWeight s)) =
        ↑Xminus * (lowerWeight s * (starRingEnd ℂ) (lowerWeight s)) := by ring
    _ = ↑Xminus * (Real.exp (-eta s) : ℂ) := by rw [lowerWeight_mul_conj]
    _ = Complex.exp (-eta s) * (Xminus : ℂ) := by
      rw [Complex.ofReal_exp]
      rw [Complex.ofReal_neg]
      ring

/-- The upper-right circular component has phase weight `exp (iθ)`. -/
theorem lorentz_transverse_right_phase
    (s : PuncturedPlane) (Xright : ℂ) :
    let X : Mat2C := !![0, Xright; 0, 0]
    (lorentzAction s X) 0 1 =
      Complex.exp (Complex.I * (theta s : ℂ)) * Xright := by
  dsimp [lorentzAction, groupElement]
  simp [Matrix.mul_apply, Matrix.conjTranspose, Fin.sum_univ_two]
  rw [mul_assoc]
  calc
    upperWeight s * (Xright * (starRingEnd ℂ) (lowerWeight s)) =
        Xright * (upperWeight s * (starRingEnd ℂ) (lowerWeight s)) := by ring
    _ = Xright * Complex.exp (Complex.I * (theta s : ℂ)) := by
      rw [upperWeight_mul_conj_lower]
    _ = Complex.exp (Complex.I * (theta s : ℂ)) * Xright := by ring

/-- The lower-left circular component has phase weight `exp (-iθ)`. -/
theorem lorentz_transverse_left_phase
    (s : PuncturedPlane) (Xleft : ℂ) :
    let X : Mat2C := !![0, 0; Xleft, 0]
    (lorentzAction s X) 1 0 =
      Complex.exp (-Complex.I * (theta s : ℂ)) * Xleft := by
  dsimp [lorentzAction, groupElement]
  simp [Matrix.mul_apply, Matrix.conjTranspose, Fin.sum_univ_two]
  rw [mul_assoc]
  calc
    lowerWeight s * (Xleft * (starRingEnd ℂ) (upperWeight s)) =
        Xleft * (lowerWeight s * (starRingEnd ℂ) (upperWeight s)) := by ring
    _ = Xleft * Complex.exp (-Complex.I * (theta s : ℂ)) := by
      rw [lowerWeight_mul_conj_upper]
    _ = Complex.exp (-(Complex.I * (theta s : ℂ))) * Xleft := by
      rw [neg_mul]
      ring

/-- On `Re s = 1/2`, the boost part vanishes and the Cartan element is a
pure compact diagonal phase. -/
theorem critical_line_pure_rotation
    (s : PuncturedPlane)
    (hcrit : s.1.re = 1 / 2) :
    groupElement s =
      !![Complex.exp (Complex.I * (theta s : ℂ) / 2), 0;
         0, Complex.exp (-Complex.I * (theta s : ℂ) / 2)] := by
  have heta : eta s = 0 := by
    change s.1.re = 1 / 2 at hcrit
    exact (InfoGeometry.Apollonius.eta_zero_iff_re_eq_half s).mpr hcrit
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [groupElement, upperWeight, lowerWeight, cartanCoordinate, heta] <;>
    congr 1 <;>
    ring

end InfoGeometry.PauliLift
