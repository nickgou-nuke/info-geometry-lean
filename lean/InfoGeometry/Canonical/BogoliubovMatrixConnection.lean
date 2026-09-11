import InfoGeometry.Canonical.Mat2
import InfoGeometry.Algebra.FiniteSpinAlgebra
import Mathlib.Tactic

/-!
# Native two-by-two frame connections

This module extends the repository's native `Matrix (Fin 2) (Fin 2) ℝ`
carrier.  It records two finite matrix identities: the pullback of an
orthogonal frame is skew, and the standard hyperbolic frame has constant
off-diagonal Maurer--Cartan coefficient.  No physical interpretation is part
of these statements.
-/

namespace InfoGeometry.Canonical.Mat2

open scoped Matrix

abbrev RealCarrier := Carrier ℝ

def frameConnection (E dE : RealCarrier) : RealCarrier := E.transpose * dE

def rotationFrame (c s : ℝ) : RealCarrier := !![c, -s; s, c]

def rotationDerivative (c s : ℝ) : RealCarrier := !![-s, -c; c, -s]

def splitMetric : RealCarrier := !![(1 : ℝ), 0; 0, -1]

def hyperbolicFrame (ch sh : ℝ) : RealCarrier := !![ch, sh; sh, ch]

def hyperbolicDerivative (ch sh : ℝ) : RealCarrier := !![sh, ch; ch, sh]

def hyperbolicInverse (ch sh : ℝ) : RealCarrier := !![ch, -sh; -sh, ch]

def rotationGenerator : RealCarrier := !![(0 : ℝ), -1; 1, 0]

def offDiagonalGenerator : RealCarrier := !![(0 : ℝ), 1; 1, 0]

theorem frameConnection_skew
    (E dE : RealCarrier)
    (h : dE.transpose * E + E.transpose * dE = 0) :
    frameConnection E dE + (frameConnection E dE).transpose = 0 := by
  unfold frameConnection
  rw [Matrix.transpose_mul]
  rw [add_comm]
  exact h

theorem rotation_frameConnection
    (c s : ℝ) (h : c ^ 2 + s ^ 2 = 1) :
    frameConnection (rotationFrame c s) (rotationDerivative c s) =
      rotationGenerator := by
  ext i j
  fin_cases i <;> fin_cases j
  all_goals simp [frameConnection, rotationFrame, rotationDerivative,
    rotationGenerator, Matrix.mul_apply, Fin.sum_univ_two]
  all_goals nlinarith [h]

theorem hyperbolic_frame_isometry
    (ch sh : ℝ) (h : ch ^ 2 - sh ^ 2 = 1) :
    (hyperbolicFrame ch sh).transpose * splitMetric * hyperbolicFrame ch sh =
      splitMetric := by
  ext i j
  fin_cases i <;> fin_cases j
  all_goals simp [hyperbolicFrame, splitMetric, Matrix.mul_apply,
    Fin.sum_univ_two]
  all_goals nlinarith [h]

theorem hyperbolic_frameConnection
    (ch sh : ℝ) (h : ch ^ 2 - sh ^ 2 = 1) :
    hyperbolicInverse ch sh * hyperbolicDerivative ch sh =
      offDiagonalGenerator := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [hyperbolicInverse, hyperbolicDerivative, offDiagonalGenerator,
      Matrix.mul_apply, Fin.sum_univ_two]
    <;> nlinarith

theorem hyperbolic_inverse_left
    (ch sh : ℝ) (h : ch ^ 2 - sh ^ 2 = 1) :
    hyperbolicInverse ch sh * hyperbolicFrame ch sh = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [hyperbolicInverse, hyperbolicFrame, Matrix.mul_apply,
      Fin.sum_univ_two]
    <;> nlinarith

theorem hyperbolic_connection_split_metric_skew
    (ch sh : ℝ) (h : ch ^ 2 - sh ^ 2 = 1) :
    splitMetric * (hyperbolicInverse ch sh * hyperbolicDerivative ch sh) +
        (hyperbolicInverse ch sh * hyperbolicDerivative ch sh).transpose *
          splitMetric = 0 := by
  rw [hyperbolic_frameConnection ch sh h]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [splitMetric, offDiagonalGenerator, Matrix.mul_apply,
      Fin.sum_univ_two]

end InfoGeometry.Canonical.Mat2
