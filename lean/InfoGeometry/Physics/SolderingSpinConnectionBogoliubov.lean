import Mathlib.Tactic

/-!
# Soldering forms, spin connection, and Bogoliubov frame bundle

This module formalizes algebraic cores of the bridge:

* Pauli soldering identifies a 4-vector with a `2×2` biquaternion matrix.
* The determinant is the Minkowski interval and the characteristic equation is the lightcone.
* A tetrad/soldering form builds the metric `g = eᵀ η e`.
* A Bogoliubov boost frame preserves the Krein/CAR form when `c²-s²=1`.

The formal content is finite: determinant identities for the Pauli soldering map,
the diagonal tetrad metric identity, and Krein preservation for the `SO(1,1)`
Bogoliubov frame.
-/

noncomputable section

namespace InfoGeometry.Physics.SolderingSpinConnectionBogoliubov

open Matrix

abbrev M2C := Matrix (Fin 2) (Fin 2) ℂ
abbrev M2R := Matrix (Fin 2) (Fin 2) ℝ
abbrev M4R := Matrix (Fin 4) (Fin 4) ℝ

/-! ## Pauli soldering form -/

def σ1 : M2C := !![0, 1; 1, 0]
def σ2 : M2C := !![0, -Complex.I; Complex.I, 0]
def σ3 : M2C := !![1, 0; 0, -1]

/-- Soldering form: vector coefficients become a Hermitian/biquaternion matrix. -/
def solder (t x y z : ℂ) : M2C := t • (1 : M2C) + x • σ1 + y • σ2 + z • σ3

/-- Determinant of the soldered vector is the Minkowski quadratic form. -/
theorem solder_det (t x y z : ℂ) :
    (solder t x y z).det = t^2 - x^2 - y^2 - z^2 := by
  simp [solder, σ1, σ2, σ3, Matrix.det_fin_two, Matrix.smul_apply, Matrix.add_apply]
  ring_nf
  rw [Complex.I_sq]
  ring

/-- Characteristic equation gives lightcone coordinates. -/
theorem solder_char (lam t x y z : ℂ) :
    ((lam • (1 : M2C)) - solder t x y z).det = (lam - t)^2 - (x^2 + y^2 + z^2) := by
  simp [solder, σ1, σ2, σ3, Matrix.det_fin_two, Matrix.smul_apply, Matrix.sub_apply, Matrix.add_apply]
  ring_nf
  rw [Complex.I_sq]
  ring

theorem solder_trace (t x y z : ℂ) :
    Matrix.trace (solder t x y z) = 2 * t := by
  simp [solder, σ1, σ2, σ3, Matrix.trace_fin_two,
    Matrix.smul_apply, Matrix.add_apply]
  ring

/-! ## Tetrad metric construction -/

/-- Minkowski metric in internal frame. -/
def eta4 : M4R := diagonal ![1, -1, -1, -1]

/-- Diagonal tetrad/soldering frame. -/
def tetradDiag (e0 e1 e2 e3 : ℝ) : M4R := diagonal ![e0, e1, e2, e3]

/-- Metric induced by a tetrad: `g=eᵀηe`. -/
def inducedMetric (e : M4R) : M4R := eᵀ * eta4 * e

/-- Diagonal tetrad gives diagonal Lorentzian metric. -/
theorem inducedMetric_diag (e0 e1 e2 e3 : ℝ) :
    inducedMetric (tetradDiag e0 e1 e2 e3) = diagonal ![e0^2, -(e1^2), -(e2^2), -(e3^2)] := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [inducedMetric, tetradDiag, eta4, Matrix.mul_apply, diagonal] <;>
    ring

/-! ## Bogoliubov/Krein frame atom -/

/-- `SO(1,1)`/Bogoliubov boost frame. -/
def bogoliubov (c s : ℝ) : M2R := !![c, s; s, c]

/-- Krein/CAR metric. -/
def kreinJ : M2R := !![1, 0; 0, -1]

/-- Bogoliubov frame preserves the Krein form when `c²-s²=1`. -/
theorem bogoliubov_preserves_krein (c s : ℝ) (h : c^2 - s^2 = 1) :
    (bogoliubov c s)ᵀ * kreinJ * (bogoliubov c s) = kreinJ := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [bogoliubov, kreinJ, Matrix.mul_apply, Fin.sum_univ_two] <;>
    nlinarith

#check solder_det
#check solder_char
#check inducedMetric_diag
#check bogoliubov_preserves_krein

end InfoGeometry.Physics.SolderingSpinConnectionBogoliubov
