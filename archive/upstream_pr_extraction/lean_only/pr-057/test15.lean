import Mathlib.Tactic
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Calculus.Deriv.Comp
import Mathlib.Analysis.Calculus.Deriv.Smul
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import InfoGeometry.Canonical.TopologicalKMSFlow

open InfoGeometry.Canonical.TopologicalKMSFlow
open InfoGeometry.Clifford.Cl44Witt
open InfoGeometry.Clifford

noncomputable section

variable (E μ : Fin 4 → ℝ) (i : Fin 4)

theorem hasDerivAt_cosh_sub_sinh (w t : ℝ) :
    HasDerivAt (fun t' => Real.cosh (t' * w) - Real.sinh (t' * w))
               (-w * (Real.cosh (t * w) - Real.sinh (t * w))) t := by
  have h1 : HasDerivAt (fun t' => Real.cosh (t' * w)) (Real.sinh (t * w) * w) t := by
    exact HasDerivAt.comp t (hasDerivAt_cosh (t * w)) (hasDerivAt_mul_const w)
  have h2 : HasDerivAt (fun t' => Real.sinh (t' * w)) (Real.cosh (t * w) * w) t := by
    exact HasDerivAt.comp t (hasDerivAt_sinh (t * w)) (hasDerivAt_mul_const w)
  have h3 := HasDerivAt.sub h1 h2
  convert h3 using 1
  ring

theorem hasDerivAt_modularFlow_aVec (t : ℝ) :
    HasDerivAt (fun t' => boostFun E μ t' (aVec i))
               (-ω E μ i • boostFun E μ t (aVec i)) t := by
  have h_eq : (fun t' => boostFun E μ t' (aVec i)) = fun t' => (Real.cosh (t' * ω E μ i) - Real.sinh (t' * ω E μ i)) • aVec i := by
    ext t'
    exact modularFlow_aVec E μ t' i
  rw [h_eq]
  have hd := hasDerivAt_cosh_sub_sinh (ω E μ i) t
  have hd2 := HasDerivAt.smul_const hd (aVec i)
  rw [modularFlow_aVec E μ t i]
  convert hd2 using 1
  simp only [neg_mul]
  rw [neg_smul]
  congr 1
  rw [mul_smul]
