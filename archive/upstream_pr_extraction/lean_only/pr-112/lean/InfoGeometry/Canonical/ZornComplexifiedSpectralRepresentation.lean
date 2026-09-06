import InfoGeometry.Canonical.ZornLeftRegularRepresentation
import Mathlib.LinearAlgebra.Matrix.ToLin

/-!
# Complexified spectral carrier for Zorn left multiplication

The native Zorn product is non-associative, but left multiplication is a real
linear map on the eight-coordinate carrier.  This file defines its honest
entrywise complexification as a `8 × 8` complex matrix.  No characteristic
polynomial or eigenvalue claim is made here; those require a separately proved
matrix-level invariant.
-/

namespace InfoGeometry.Canonical.ZornComplexifiedSpectralRepresentation

open InfoGeometry.Algebra
open InfoGeometry.Canonical.ZornLeftRegularRepresentation

abbrev ComplexCoord := Fin 8 → ℂ

noncomputable def complexifiedLeftRegularMatrix (F : ZM) :
    Matrix (Fin 8) (Fin 8) ℂ := fun i j =>
  (leftRegular F (Pi.single j (1 : ℝ)) i : ℂ)

noncomputable abbrev complexifiedLeftRegular (F : ZM) :
    ComplexCoord →ₗ[ℂ] ComplexCoord :=
  (complexifiedLeftRegularMatrix F).mulVecLin

@[simp] theorem complexifiedLeftRegular_apply (F : ZM) (x : ComplexCoord) :
    complexifiedLeftRegular F x =
      Matrix.mulVec (complexifiedLeftRegularMatrix F) x := by
  rfl

theorem complexifiedLeftRegular_isLinear (F : ZM) :
    IsLinearMap ℂ (complexifiedLeftRegular F) := by
  exact (complexifiedLeftRegular F).isLinear

end InfoGeometry.Canonical.ZornComplexifiedSpectralRepresentation
