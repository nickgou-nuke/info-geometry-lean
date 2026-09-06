import Mathlib

noncomputable section

namespace InfoGeometry.Arithmetic.MajoranaPolyaHilbert

def finiteRelativeDeterminant {n : Type*} [Fintype n] [DecidableEq n]
    (A B : Matrix n n ℝ) : ℝ :=
  Matrix.det (A - B)

theorem finiteRelativeDeterminant_translation_invariant
    {n : Type*} [Fintype n] [DecidableEq n]
    (A B C : Matrix n n ℝ) :
    finiteRelativeDeterminant (A + C) (B + C) =
      finiteRelativeDeterminant A B := by
  unfold finiteRelativeDeterminant
  congr 1
  ext i j
  simp

theorem finiteRelativeDeterminant_self
    {n : Type*} [Fintype n] [DecidableEq n] [Nonempty n]
    (A : Matrix n n ℝ) :
    finiteRelativeDeterminant A A = 0 := by
  unfold finiteRelativeDeterminant
  rw [sub_self, Matrix.det_zero (inferInstance : Nonempty n)]

/-! ## 7. Relative determinant/scattering MBK target -/

/--
Relative determinant/scattering packet for the MBK program.

This is the narrow next target after the finite Majorana/Witten-character
layers.  It asks for one real self-adjoint relative MBK operator together with
the Hestenes--Krein/categorical colimit data needed to identify its relative
determinant or scattering trace with the completed critical-line readout
`Xi(t) = xi(1/2 + it)`.

All hard colimit assertions are fields.  In particular, this structure does not
construct the operator, prove a Fredholm determinant identity, prove the
Riemann--Weil explicit formula, or prove RH.
-/
structure RelativeMBKDeterminantScatteringData
    (Operator ScatteringMatrix DeterminantReadout : Type) where
  diracCutoff : Operator
  diracFree : Operator
  relativeDeterminant : DeterminantReadout
  scatteringPhase : ScatteringMatrix

end InfoGeometry.Arithmetic.MajoranaPolyaHilbert
