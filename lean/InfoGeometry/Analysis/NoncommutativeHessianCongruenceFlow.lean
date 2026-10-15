import Mathlib.Analysis.Matrix.Normed
import InfoGeometry.Algebra.FiniteSpinAlgebra
import Mathlib.Analysis.Calculus.Deriv.Mul

/-!
# Noncommutative Hessian congruence flow

The congruence `Uᵀ * H₀ * U` is kept as an ordered matrix product.  The
resulting derivative is the Lyapunov expression `Aᵀ * H + H * A`; no factor
commutation or diagonalization is used.
-/

noncomputable section

open scoped Matrix.Norms.Frobenius

attribute [-instance] instTopologicalSpaceMatrix Matrix.addCommGroup Matrix.module

namespace InfoGeometry.Analysis.NoncommutativeHessianCongruenceFlow

variable {n : Type*} [Fintype n] [DecidableEq n]

local instance (priority := 3000) : AddCommGroup (Matrix n n ℝ) :=
  (Matrix.frobeniusNormedRing : NormedRing (Matrix n n ℝ)).toAddCommGroup

local instance (priority := 3000) : Module ℝ (Matrix n n ℝ) :=
  letI : NormedRing (Matrix n n ℝ) := Matrix.frobeniusNormedRing
  letI : NormedAlgebra ℝ (Matrix n n ℝ) := Matrix.frobeniusNormedAlgebra
  (NormedAlgebra.toNormedSpace (Matrix n n ℝ)).toModule

def hessianCongruencePath
    (U : ℝ → Matrix n n ℝ) (H₀ : Matrix n n ℝ) :
    ℝ → Matrix n n ℝ :=
  fun t => (U t).transpose * H₀ * U t

theorem hasDerivAt_hessianCongruence
    {U Udot : ℝ → Matrix n n ℝ}
    {H₀ : Matrix n n ℝ} {t : ℝ}
    (hU : HasDerivAt U (Udot t) t)
    (hUt : HasDerivAt
      (fun s => (U s).transpose) ((Udot t).transpose) t) :
    HasDerivAt
      (hessianCongruencePath U H₀)
      ((Udot t).transpose * H₀ * U t +
        (U t).transpose * H₀ * Udot t) t := by
  have hleft := hUt.mul (hasDerivAt_const t H₀)
  have hall := hleft.mul hU
  convert hall using 1
  · ext s
    simp [hessianCongruencePath, Matrix.mul_assoc]
  · simp [Matrix.mul_assoc]

theorem hasDerivAt_hessianCongruence_of_right_generator
    {U Udot : ℝ → Matrix n n ℝ}
    {A : ℝ → Matrix n n ℝ} {H₀ : Matrix n n ℝ} {t : ℝ}
    (hU : HasDerivAt U (Udot t) t)
    (hUt : HasDerivAt
      (fun s => (U s).transpose) ((Udot t).transpose) t)
    (hright : Udot t = U t * A t) :
    HasDerivAt
      (hessianCongruencePath U H₀)
      ((A t).transpose *
          ((U t).transpose * H₀ * U t) +
        ((U t).transpose * H₀ * U t) * A t) t := by
  have h := hasDerivAt_hessianCongruence (H₀ := H₀) hU hUt
  rw [hright] at h
  convert h using 1
  rw [Matrix.transpose_mul]
  simp only [Matrix.mul_assoc]

end InfoGeometry.Analysis.NoncommutativeHessianCongruenceFlow
