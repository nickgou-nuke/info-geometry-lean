import InfoGeometry.Algebra.ZornVectorMatrix
import InfoGeometry.Algebra.FiniteSpinAlgebra
import Mathlib

noncomputable section

namespace InfoGeometry.Lie.CanonicalZornG2FrameProbe

abbrev RationalVZ := InfoGeometry.Algebra.ZornVectorMatrix ℚ

def rationalAxis (i : Fin 3) : Fin 3 → ℚ := Pi.single i 1

def rationalFrameVector (a b : ℚ) (v w : Fin 3 → ℚ) : RationalVZ :=
  ⟨a, v, w, b⟩

def rationalCircularFrame : Fin 8 → RationalVZ
  | 0 => rationalFrameVector (1 / 2 : ℚ) (1 / 2 : ℚ) 0 0
  | 1 => rationalFrameVector 0 0 ((1 / 2 : ℚ) • rationalAxis 0) ((1 / 2 : ℚ) • rationalAxis 0)
  | 2 => rationalFrameVector 0 0 ((1 / 2 : ℚ) • rationalAxis 1) ((1 / 2 : ℚ) • rationalAxis 1)
  | 3 => rationalFrameVector 0 0 ((1 / 2 : ℚ) • rationalAxis 2) ((1 / 2 : ℚ) • rationalAxis 2)
  | 4 => rationalFrameVector (1 / 2 : ℚ) (-1 / 2 : ℚ) 0 0
  | 5 => rationalFrameVector 0 0 (-(1 / 2 : ℚ) • rationalAxis 0) ((1 / 2 : ℚ) • rationalAxis 0)
  | 6 => rationalFrameVector 0 0 (-(1 / 2 : ℚ) • rationalAxis 1) ((1 / 2 : ℚ) • rationalAxis 1)
  | 7 => rationalFrameVector 0 0 (-(1 / 2 : ℚ) • rationalAxis 2) ((1 / 2 : ℚ) • rationalAxis 2)
  | _ => 0

def rationalCoordinates (X : RationalVZ) : Fin 8 → ℚ
  | 0 => X.a
  | 1 => X.v 0
  | 2 => X.v 1
  | 3 => X.v 2
  | 4 => X.b
  | 5 => X.w 0
  | 6 => X.w 1
  | 7 => X.w 2
  | _ => 0

def rationalCircularFrameMatrix : Matrix (Fin 8) (Fin 8) ℚ :=
  fun i j => rationalCoordinates (rationalCircularFrame j) i

def frameLiteral : Matrix (Fin 8) (Fin 8) ℚ :=
  !![(1 / 2 : ℚ), 0, 0, 0, (1 / 2 : ℚ), 0, 0, 0;
      0, (1 / 2 : ℚ), 0, 0, 0, (-1 / 2 : ℚ), 0, 0;
      0, 0, (1 / 2 : ℚ), 0, 0, 0, (-1 / 2 : ℚ), 0;
      0, 0, 0, (1 / 2 : ℚ), 0, 0, 0, (-1 / 2 : ℚ);
      (1 / 2 : ℚ), 0, 0, 0, (-1 / 2 : ℚ), 0, 0, 0;
      0, (1 / 2 : ℚ), 0, 0, 0, (1 / 2 : ℚ), 0, 0;
      0, 0, (1 / 2 : ℚ), 0, 0, 0, (1 / 2 : ℚ), 0;
      0, 0, 0, (1 / 2 : ℚ), 0, 0, 0, (1 / 2 : ℚ)]


theorem frame_matrix_eq_literal : rationalCircularFrameMatrix = frameLiteral := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [rationalCircularFrameMatrix, frameLiteral, rationalCircularFrame,
      rationalFrameVector, rationalAxis, rationalCoordinates, Pi.single_apply] <;>
    omega


end InfoGeometry.Lie.CanonicalZornG2FrameProbe
