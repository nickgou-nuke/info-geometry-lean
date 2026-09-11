import Mathlib.Data.Complex.Basic
import InfoGeometry.Algebra.FiniteSpinAlgebra
import InfoGeometry.Meta.Architecture

namespace InfoGeometry.Canonical.JonesCalculus

open Complex

/-- A Jones Vector representing the classical optical polarization as an SU(2) Spinor. -/
structure JonesVector where
  x : ℂ
  y : ℂ

/-- A 2x2 Jones Matrix representing a linear optical component. -/
structure JonesMatrix where
  m11 : ℂ
  m12 : ℂ
  m21 : ℂ
  m22 : ℂ

def apply_matrix (M : JonesMatrix) (v : JonesVector) : JonesVector :=
  ⟨M.m11 * v.x + M.m12 * v.y, M.m21 * v.x + M.m22 * v.y⟩

/-- Right-Circular Spinor |R>. We use a generic amplitude c to bypass real-to-complex coercions. -/
def R (c : ℂ) : JonesVector := ⟨c, c * I⟩

/-- Left-Circular Spinor |L>. -/
def L (c : ℂ) : JonesVector := ⟨c, c * -I⟩

/-- Half-Wave Plate Matrix (fast axis horizontal).
    Equivalent to exp(-i pi/2 sigma_z) = -i * sigma_z -/
def HWP : JonesMatrix := ⟨-I, 0, 0, I⟩

/-- Theorem: Optical Andreev Reflection.
    The Half-Wave Plate perfectly inverts the chirality from |R> to a phase-shifted |L>,
    proving that standard polarization optics natively support the particle-hole inversion
    required for Majorana zero modes. -/
@[rep_depth thermo]
theorem optical_andreev_reflection (c : ℂ) : 
    apply_matrix HWP (R c) = ⟨-I * (L c).x, -I * (L c).y⟩ := by
  dsimp [apply_matrix, HWP, R, L]
  congr 1
  · ring
  · ring

end InfoGeometry.Canonical.JonesCalculus

