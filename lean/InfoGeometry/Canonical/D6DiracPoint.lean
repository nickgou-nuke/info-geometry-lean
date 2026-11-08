import InfoGeometry.Canonical.D6DiracSpectralBridge
import InfoGeometry.Algebra.FiniteSpinAlgebra
import InfoGeometry.Canonical.D6ReciprocalLatticeBrillouinZone
import Mathlib.Tactic

/-!
# Algebraic Dirac-point theorem at the reciprocal origin

This file isolates the finite two-band degeneracy at the origin.  It does not
claim a global band-topology or a continuum Dirac-cone theorem.
-/

namespace InfoGeometry.Canonical.D6DiracPoint

open InfoGeometry.Canonical.D6DiracSpectralBridge
open InfoGeometry.Canonical.D6ReciprocalLatticeBrillouinZone

def masslessDiracBlock (p : Fin 2 → ℝ) : H2 :=
  diracBlock 0 (p 0) (p 1)

def reciprocalOrigin : Fin 2 → ℝ := ![0, 0]

def realHexStar (k : InfoGeometry.Canonical.D6SixModeAction.D6Index) : Fin 2 → ℝ :=
  fun i => (hexStar k i : ℝ)

theorem masslessDirac_shiftedDeterminant (p : Fin 2 → ℝ) (lam : ℝ) :
    shiftedDeterminant (masslessDiracBlock p) lam = lam ^ 2 - p 0 * p 1 := by
  simpa [masslessDiracBlock, pow_two] using
    (diracBlock_shiftedDeterminant 0 (p 0) (p 1) lam)

theorem realHexStar_shiftedDeterminant
    (k : InfoGeometry.Canonical.D6SixModeAction.D6Index) (lam : ℝ) :
    shiftedDeterminant (masslessDiracBlock (realHexStar k)) lam =
      lam ^ 2 - realHexStar k 0 * realHexStar k 1 := by
  exact masslessDirac_shiftedDeterminant (realHexStar k) lam

theorem masslessDiracBlock_at_origin :
    masslessDiracBlock reciprocalOrigin = !![0, 0; 0, 0] := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [masslessDiracBlock, reciprocalOrigin, diracBlock]

theorem masslessDirac_origin_shiftedDeterminant (lam : ℝ) :
    shiftedDeterminant (masslessDiracBlock reciprocalOrigin) lam = lam ^ 2 := by
  rw [masslessDiracBlock_at_origin]
  simp [shiftedDeterminant, Matrix.det_fin_two, Matrix.sub_apply, Matrix.smul_apply]
  ring

theorem masslessDirac_origin_zero_determinant :
    shiftedDeterminant (masslessDiracBlock reciprocalOrigin) 0 = 0 := by
  simpa using masslessDirac_origin_shiftedDeterminant 0

theorem reciprocalOrigin_not_hexagonalBoundary :
    ¬ hexagonalBrillouinBoundary reciprocalOrigin := by
  simp [hexagonalBrillouinBoundary, reciprocalOrigin]

end InfoGeometry.Canonical.D6DiracPoint
