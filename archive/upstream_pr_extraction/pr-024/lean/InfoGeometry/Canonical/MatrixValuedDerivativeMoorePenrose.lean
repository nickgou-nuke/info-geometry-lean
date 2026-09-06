import Mathlib
import InfoGeometry.Canonical.MoorePenrose

/-!
# Matrix-valued derivative with a Moore-Penrose quotient

This file formalizes the finite algebraic core of the 1977 matrix-valued
derivative paper:

* the generalized difference quotient is the right quotient
  `(f(X + H) - f X) * H⁺`;
* left multiplication by a fixed matrix commutes with that quotient;
* a concrete singular `2 × 2` projector is its own Moore-Penrose inverse;
* the square map at the zero matrix closes by entrywise calculation.

The analytic limit theory is not claimed here.  That part remains the job of
the external calculus and limit-state lanes.
-/

namespace InfoGeometry.Canonical.MatrixValuedDerivativeMoorePenrose

open InfoGeometry.Canonical.MoorePenrose

noncomputable section

abbrev Mat2 := Matrix (Fin 2) (Fin 2) ℚ

/-- The generalized difference quotient `[(f(X+H)-f(X))]H⁺`. -/
def generalizedDifferenceQuotient {R : Type*} [Ring R] (f : R → R)
    (X H Hplus : R) : R :=
  (f (X + H) - f X) * Hplus

/-- Constant functions have zero generalized difference quotient. -/
theorem generalizedDifferenceQuotient_const {R : Type*} [Ring R]
    (c : R) (X H Hplus : R) :
    generalizedDifferenceQuotient (fun _ : R => c) X H Hplus = 0 := by
  simp [generalizedDifferenceQuotient]

/--
The generalized difference quotient is left-linear: a fixed left factor can be
pushed outside the quotient.
-/
theorem generalizedDifferenceQuotient_left_mul {R : Type*} [Ring R]
    (A : R) (f : R → R) (X H Hplus : R) :
    generalizedDifferenceQuotient (fun Z => A * f Z) X H Hplus =
      A * generalizedDifferenceQuotient f X H Hplus := by
  calc
    (A * f (X + H) - A * f X) * Hplus = (A * (f (X + H) - f X)) * Hplus := by
      rw [← mul_sub]
    _ = A * ((f (X + H) - f X) * Hplus) := by
      rw [mul_assoc]

/-- A singular projector used as an explicit exact-rational Moore-Penrose example. -/
def singularProjector : Mat2 := !![1, 0; 0, 0]

/-- The projector is its own Moore-Penrose inverse in this finite model. -/
def singularProjectorPlus : Mat2 := singularProjector

/-- Exact Penrose equations for the singular projector. -/
theorem singularProjector_isMoorePenrose :
    IsMoorePenroseInverse singularProjector singularProjectorPlus := by
  refine IsMoorePenroseInverse.mk ?_ ?_ ?_ ?_
  · ext i j
    fin_cases i <;> fin_cases j <;>
      simp [singularProjector, singularProjectorPlus, Matrix.mul_apply, Fin.sum_univ_two]
  · ext i j
    fin_cases i <;> fin_cases j <;>
      simp [singularProjector, singularProjectorPlus, Matrix.mul_apply, Fin.sum_univ_two]
  · ext i j
    fin_cases i <;> fin_cases j <;>
      simp [singularProjector, singularProjectorPlus, Matrix.mul_apply, Fin.sum_univ_two]
  · ext i j
    fin_cases i <;> fin_cases j <;>
      simp [singularProjector, singularProjectorPlus, Matrix.mul_apply, Fin.sum_univ_two]

/-- The square map at the zero matrix closes on the singular projector. -/
theorem square_generalizedDifferenceQuotient_zero :
    generalizedDifferenceQuotient (fun M : Mat2 => M * M) 0
        singularProjector singularProjectorPlus = singularProjector := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [generalizedDifferenceQuotient, singularProjector, singularProjectorPlus,
      Matrix.mul_apply, Fin.sum_univ_two]

/-- Constant matrix-valued functions have zero quotient in the concrete example. -/
theorem constant_generalizedDifferenceQuotient_zero (c : Mat2) :
    generalizedDifferenceQuotient (fun _ : Mat2 => c) 0
        singularProjector singularProjectorPlus = 0 := by
  simp [generalizedDifferenceQuotient]

end

end InfoGeometry.Canonical.MatrixValuedDerivativeMoorePenrose
