import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Tactic

/-!
# Rank-two chiral Cartan torus

The full three-colour diagonal weight system is represented by a trace-zero
Cartan plane.  This owner records only the finite coordinate change from
additive logarithmic parameters to determinant-one positive coordinates and
the corresponding Laplace/logarithmic-Mellin kernel identity.

No integration, inversion, analytic continuation, or continuum limit is
claimed here.  Those belong to the existing analysis owners or to the
categorical colimit layer.
-/

noncomputable section

namespace InfoGeometry.Canonical.ChiralCartanTorusLaplaceMellinBridge

/-- Two independent coordinates on the rank-two trace-zero Cartan plane. -/
structure CartanPoint where
  t₁ : ℝ
  t₂ : ℝ

/-- The dependent third Cartan coordinate. -/
def CartanPoint.t₃ (t : CartanPoint) : ℝ :=
  -(t.t₁ + t.t₂)

@[simp] theorem CartanPoint.trace_zero (t : CartanPoint) :
    t.t₁ + t.t₂ + t.t₃ = 0 := by
  simp [CartanPoint.t₃]
  ring

/-- Positive multiplicative coordinates `zᵢ = exp (2 tᵢ)`. -/
def CartanPoint.z₁ (t : CartanPoint) : ℝ := Real.exp (2 * t.t₁)

def CartanPoint.z₂ (t : CartanPoint) : ℝ := Real.exp (2 * t.t₂)

def CartanPoint.z₃ (t : CartanPoint) : ℝ := Real.exp (2 * t.t₃)

@[simp] theorem CartanPoint.z₁_pos (t : CartanPoint) : 0 < t.z₁ :=
  Real.exp_pos _

@[simp] theorem CartanPoint.z₂_pos (t : CartanPoint) : 0 < t.z₂ :=
  Real.exp_pos _

@[simp] theorem CartanPoint.z₃_pos (t : CartanPoint) : 0 < t.z₃ :=
  Real.exp_pos _

@[simp] theorem CartanPoint.z_product_one (t : CartanPoint) :
    t.z₁ * t.z₂ * t.z₃ = 1 := by
  unfold CartanPoint.z₁ CartanPoint.z₂ CartanPoint.z₃
  rw [← Real.exp_add, ← Real.exp_add]
  simp [CartanPoint.t₃]
  ring

/-- A finite Laplace character on the additive Cartan plane. -/
def laplaceKernel (s : ℝ × ℝ × ℝ) (t : CartanPoint) : ℝ :=
  Real.exp (-(s.1 * t.t₁ + s.2.1 * t.t₂ + s.2.2 * t.t₃))

/-- The same character read in logarithmic multiplicative coordinates. -/
def logarithmicMellinKernel (s : ℝ × ℝ × ℝ) (t : CartanPoint) : ℝ :=
  Real.exp (-((s.1 / 2) * Real.log t.z₁ +
    (s.2.1 / 2) * Real.log t.z₂ +
    (s.2.2 / 2) * Real.log t.z₃))

theorem laplaceKernel_eq_logarithmicMellinKernel
    (s : ℝ × ℝ × ℝ) (t : CartanPoint) :
    laplaceKernel s t = logarithmicMellinKernel s t := by
  unfold laplaceKernel logarithmicMellinKernel
  simp [CartanPoint.z₁, CartanPoint.z₂, CartanPoint.z₃]
  ring

theorem log_z₁_eq_two_mul_t₁ (t : CartanPoint) :
    Real.log t.z₁ = 2 * t.t₁ := by
  simp [CartanPoint.z₁]

theorem log_z₂_eq_two_mul_t₂ (t : CartanPoint) :
    Real.log t.z₂ = 2 * t.t₂ := by
  simp [CartanPoint.z₂]

theorem log_z₃_eq_two_mul_t₃ (t : CartanPoint) :
    Real.log t.z₃ = 2 * t.t₃ := by
  simp [CartanPoint.z₃]

end InfoGeometry.Canonical.ChiralCartanTorusLaplaceMellinBridge
