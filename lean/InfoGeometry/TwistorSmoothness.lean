import Mathlib.Data.Matrix.Basic
import InfoGeometry.Algebra.FiniteSpinAlgebra
import Mathlib.Data.Complex.Basic
import Mathlib.LinearAlgebra.Matrix.Notation
import InfoGeometry.MellinColimitTrifactor
import InfoGeometry.Categorical.ModularDoubledRealTwistorColimit

/-!
# Twistor Fibration + Smoothness as Colimit — Lean 4

CP³ → S⁴ : twistor projection (fiber S²)
S⁷ → S⁴ : quaternionic Hopf (fiber S³)
Relation: S⁷ → CP³ (U(1)) → S⁴

Smoothness = colimit of Mellin-bound discrete structures:
  Cl(1,1)⁵ = Cl(5,5) → colimit → Cl(∞,∞)
  det∈{-1,0,1} survives the limit.
-/

noncomputable section

namespace TwistorSmoothness

open Matrix

/-- Pauli matrices as quaternion basis. -/
def I2 : Matrix (Fin 2) (Fin 2) ℂ := !![1, 0; 0, 1]
def s1 : Matrix (Fin 2) (Fin 2) ℂ := !![0, 1; 1, 0]
def s2 : Matrix (Fin 2) (Fin 2) ℂ := !![0, -Complex.I; Complex.I, 0]
def s3 : Matrix (Fin 2) (Fin 2) ℂ := !![1, 0; 0, -1]

/-- A quaternion q = a·I + b·(iσ₁) + c·(iσ₂) + d·(iσ₃). -/
def quaternion (a b c d : ℝ) : Matrix (Fin 2) (Fin 2) ℂ :=
  (a : ℂ) • I2 + (b : ℂ) • (Complex.I • s1) + (c : ℂ) • (Complex.I • s2) + (d : ℂ) • (Complex.I • s3)

/-- Quaternionic conjugate q* = a·I - b·(iσ₁) - c·(iσ₂) - d·(iσ₃). -/
def quatConj (a b c d : ℝ) : Matrix (Fin 2) (Fin 2) ℂ :=
  (a : ℂ) • I2 - (b : ℂ) • (Complex.I • s1) - (c : ℂ) • (Complex.I • s2) - (d : ℂ) • (Complex.I • s3)

/-- |q|² = q·q* = (a²+b²+c²+d²)·I. -/
theorem quaternion_norm (a b c d : ℝ) :
    quaternion a b c d * quatConj a b c d
    = ((a : ℂ)^2 + (b : ℂ)^2 + (c : ℂ)^2 + (d : ℂ)^2) • I2 := by
  unfold quaternion quatConj
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [I2, s1, s2, s3, Matrix.mul_apply, Fin.sum_univ_two]
  all_goals
    ring_nf
    try rw [show Complex.I ^ 2 = (-1 : ℂ) by simp [pow_two, Complex.I_mul_I]]
    try ring_nf

/-- det(σ₃) = -1, σ₃³ = σ₃. -/
theorem s3_trifactor : s3*s3*s3 = s3 ∧ s3.det = (-1 : ℂ) := by
  refine ⟨?_, ?_⟩
  · ext i j; fin_cases i <;> fin_cases j <;> simp [s3, Matrix.mul_apply, Fin.sum_univ_two]
  · simp [s3, Matrix.det_fin_two]

/--
Bott/trifactor finite readout: an integer tripotent has tensor-power
determinant in `{0, 1}` at the even Bott window used by the `Cl(5,5)` lane.

This delegates to `MellinColimitTrifactor`; it is a determinant-sector theorem,
not a full Clifford-algebra isomorphism.
-/
theorem bott_kernel_cl55 (d : ℤ) (h_cube : d ^ 3 = d) :
    d ^ 80 = 0 ∨ d ^ 80 = 1 :=
  MellinColimitTrifactor.bott_absorbs_negative_sector d h_cube

/-- The determinant classifier `det ∈ {-1,0,1}` is the tripotent classifier. -/
theorem trifactor_survives_limit
    {R : Type _} [CommRing R] [IsDomain R] (d : R) (h_cube : d ^ 3 = d) :
    d = 0 ∨ d = 1 ∨ d = -1 :=
  MellinColimitTrifactor.tripotent_classifier d h_cube

/--
Structural smooth-boundary readout: a stage projection has a continuum readout
only through the commuting square of the fractal scale colimit.

This is the formal replacement for the slogan "smoothness is the colimit of
Mellin-bound Cantor stages"; no smooth structure is asserted here.
-/
theorem smoothness_as_colimit
    (C :
      InfoGeometry.Categorical.ModularDoubledRealTwistorColimit.FractalScaleProjectionColimit)
    (n : ℕ) (x : C.StageTotal n) :
    C.limitProjection (C.stageToLimit n x) =
      C.baseToLimit n (C.stageProjection n x) :=
  C.stage_projection_commutes n x

end TwistorSmoothness
