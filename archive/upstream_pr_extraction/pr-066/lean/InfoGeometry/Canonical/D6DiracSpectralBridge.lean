import InfoGeometry.Canonical.D6SixModeAction
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.Tactic

/-!
# Finite D6-symmetric Dirac spectral readout

This is an algebraic two-band spectral layer.  It records the characteristic
determinant of a real `2 × 2` Dirac block and its invariance under a six-mode
`D6` family.  No lattice, analytic Brillouin zone, or Dirac-point existence
claim is introduced here.
-/

namespace InfoGeometry.Canonical.D6DiracSpectralBridge

open scoped Matrix
open InfoGeometry.Canonical.D6SixModeAction

abbrev H2 := Matrix (Fin 2) (Fin 2) ℝ

def diracBlock (m a b : ℝ) : H2 :=
  !![m, a; b, -m]

def shiftedDeterminant (H : H2) (lam : ℝ) : ℝ :=
  (H - lam • (1 : H2)).det

theorem diracBlock_shiftedDeterminant (m a b lam : ℝ) :
    shiftedDeterminant (diracBlock m a b) lam =
      (m - lam) * (-m - lam) - a * b := by
  simp [shiftedDeterminant, diracBlock, Matrix.det_fin_two,
    Matrix.sub_apply, Matrix.smul_apply]

def d6InvariantFamily (H : D6Index → H2) : Prop :=
  ∀ k i, H (i + k) = H i

theorem d6InvariantFamily_shiftedDeterminant
    (H : D6Index → H2) (hH : d6InvariantFamily H)
    (k i : D6Index) (lam : ℝ) :
    shiftedDeterminant (H (i + k)) lam = shiftedDeterminant (H i) lam := by
  rw [hH k i]

end InfoGeometry.Canonical.D6DiracSpectralBridge
