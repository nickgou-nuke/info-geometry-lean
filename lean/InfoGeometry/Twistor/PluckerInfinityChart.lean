/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.Projective.KleinQuadricPlucker
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.LinearAlgebra.Matrix.Notation

/-!
# The graph chart of the Klein quadric and its normalized interval

The two columns of `(X,1)` give a genuine decomposable Plücker vector.  Its
`p23` coordinate is one; the converse reconstructs every Klein vector in the
`p23 ≠ 0` chart, up to precisely that scale.  The polar pairing divided by
the two chart scales is the determinant of the matrix difference.

The coordinate order is `01,02,03,12,13,23`.  No real structure or spacetime
signature is selected here.  In particular this matrix graph convention is
`(Xπ,π)`; an incidence convention containing `i` needs its explicit adapter.
-/

namespace InfoGeometry.Twistor.PluckerInfinityChart

open InfoGeometry.Projective.KleinQuadricPlucker
open InfoGeometry.Projective.KleinQuadricPlucker.Plucker6

section Ring

variable {R : Type*} [CommRing R]

/-- First column of the graph frame `(X,1)`. -/
def graphFirst (X : Matrix (Fin 2) (Fin 2) R) : Vec4 R :=
  ⟨X 0 0, X 1 0, 1, 0⟩

/-- Second column of the graph frame `(X,1)`. -/
def graphSecond (X : Matrix (Fin 2) (Fin 2) R) : Vec4 R :=
  ⟨X 0 1, X 1 1, 0, 1⟩

/-- The actual minors of the two graph-frame columns. -/
def graphPlucker (X : Matrix (Fin 2) (Fin 2) R) : Plucker6 R :=
  pluckerLine (graphFirst X) (graphSecond X)

theorem graphPlucker_coordinates (X : Matrix (Fin 2) (Fin 2) R) :
    graphPlucker X = ⟨X.det, -X 0 1, X 0 0, -X 1 1, X 1 0, 1⟩ := by
  apply Plucker6.ext <;>
    simp [graphPlucker, graphFirst, graphSecond, pluckerLine, Matrix.det_fin_two]
  ring

@[simp] theorem graphPlucker_p01 (X : Matrix (Fin 2) (Fin 2) R) :
    (graphPlucker X).p01 = X.det := by rw [graphPlucker_coordinates]

@[simp] theorem graphPlucker_p02 (X : Matrix (Fin 2) (Fin 2) R) :
    (graphPlucker X).p02 = -X 0 1 := by rw [graphPlucker_coordinates]

@[simp] theorem graphPlucker_p03 (X : Matrix (Fin 2) (Fin 2) R) :
    (graphPlucker X).p03 = X 0 0 := by rw [graphPlucker_coordinates]

@[simp] theorem graphPlucker_p12 (X : Matrix (Fin 2) (Fin 2) R) :
    (graphPlucker X).p12 = -X 1 1 := by rw [graphPlucker_coordinates]

@[simp] theorem graphPlucker_p13 (X : Matrix (Fin 2) (Fin 2) R) :
    (graphPlucker X).p13 = X 1 0 := by rw [graphPlucker_coordinates]

@[simp] theorem graphPlucker_p23 (X : Matrix (Fin 2) (Fin 2) R) :
    (graphPlucker X).p23 = 1 := by rw [graphPlucker_coordinates]

@[simp] theorem kleinQ_graphPlucker (X : Matrix (Fin 2) (Fin 2) R) :
    kleinQ (graphPlucker X) = 0 :=
  kleinQ_pluckerLine _ _

theorem graphPlucker_injective :
    Function.Injective (graphPlucker (R := R)) := by
  intro X Y h
  have h00 : X 0 0 = Y 0 0 := by
    simpa using congrArg (fun P => P.p03) h
  have h01 : X 0 1 = Y 0 1 := by
    simpa using congrArg (fun P => P.p02) h
  have h10 : X 1 0 = Y 1 0 := by
    simpa using congrArg (fun P => P.p13) h
  have h11 : X 1 1 = Y 1 1 := by
    simpa using congrArg (fun P => P.p12) h
  ext i j
  fin_cases i <;> fin_cases j <;> assumption

/-- The full Klein polarization is exactly the determinant interval in this chart. -/
theorem kleinPolar_graphPlucker (X Y : Matrix (Fin 2) (Fin 2) R) :
    kleinPolar (graphPlucker X) (graphPlucker Y) = (X - Y).det := by
  simp [kleinPolar, graphPlucker_coordinates, Matrix.det_fin_two]
  ring

end Ring

section Field

variable {R : Type*} [Field R]

/-- Affine graph coordinates, interpreted on the `p23 ≠ 0` chart. -/
def chartMatrix (P : Plucker6 R) : Matrix (Fin 2) (Fin 2) R :=
  !![P.p03 / P.p23, -P.p02 / P.p23; P.p13 / P.p23, -P.p12 / P.p23]

@[simp] theorem chartMatrix_graphPlucker (X : Matrix (Fin 2) (Fin 2) R) :
    chartMatrix (graphPlucker X) = X := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [chartMatrix]

/-- The Klein equation supplies the determinant coordinate; the other four
coordinates and `p23` give the explicit affine inverse. -/
theorem reconstruct_of_klein (P : Plucker6 R) (hK : kleinQ P = 0)
    (hP : P.p23 ≠ 0) :
    P = scale P.p23 (graphPlucker (chartMatrix P)) := by
  unfold kleinQ at hK
  have h01 : P.p01 = (P.p02 * P.p13 - P.p03 * P.p12) / P.p23 := by
    apply (eq_div_iff hP).2
    linear_combination hK
  apply Plucker6.ext
  · simp [scale, graphPlucker_coordinates, chartMatrix, Matrix.det_fin_two]
    rw [h01]
    field_simp [hP]
    ring
  all_goals
    simp [scale, graphPlucker_coordinates, chartMatrix, Matrix.det_fin_two] <;>
      field_simp [hP]

/-- The projectively normalized two-point pairing.  Geometric use requires
both `p23` coordinates to be nonzero. -/
def normalizedInterval (P Q : Plucker6 R) : R :=
  kleinPolar P Q / (P.p23 * Q.p23)

theorem normalizedInterval_scale (l m : R) (hl : l ≠ 0) (hm : m ≠ 0)
    (P Q : Plucker6 R) (hP : P.p23 ≠ 0) (hQ : Q.p23 ≠ 0) :
    normalizedInterval (scale l P) (scale m Q) = normalizedInterval P Q := by
  unfold normalizedInterval
  rw [kleinPolar_scale_left, kleinPolar_scale_right]
  dsimp [scale]
  field_simp [hl, hm, hP, hQ]

@[simp] theorem normalizedInterval_graphPlucker
    (X Y : Matrix (Fin 2) (Fin 2) R) :
    normalizedInterval (graphPlucker X) (graphPlucker Y) = (X - Y).det := by
  simp [normalizedInterval, kleinPolar_graphPlucker]

/-- Every pair of finite Klein points has the same determinant interval after
explicit affine reconstruction. -/
theorem normalizedInterval_eq_det_chart_sub (P Q : Plucker6 R)
    (hPK : kleinQ P = 0) (hQK : kleinQ Q = 0)
    (hP : P.p23 ≠ 0) (hQ : Q.p23 ≠ 0) :
    normalizedInterval P Q = (chartMatrix P - chartMatrix Q).det := by
  calc
    normalizedInterval P Q =
        normalizedInterval (scale P.p23 (graphPlucker (chartMatrix P)))
          (scale Q.p23 (graphPlucker (chartMatrix Q))) :=
      congrArg₂ normalizedInterval (reconstruct_of_klein P hPK hP)
        (reconstruct_of_klein Q hQK hQ)
    _ = normalizedInterval (graphPlucker (chartMatrix P))
        (graphPlucker (chartMatrix Q)) :=
      normalizedInterval_scale _ _ hP hQ _ _ (by simp) (by simp)
    _ = _ := normalizedInterval_graphPlucker _ _

end Field

end InfoGeometry.Twistor.PluckerInfinityChart
