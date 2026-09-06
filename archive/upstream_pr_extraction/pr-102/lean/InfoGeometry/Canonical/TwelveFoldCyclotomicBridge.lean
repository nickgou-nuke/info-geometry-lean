import Mathlib.LinearAlgebra.Matrix.ToLin
import Mathlib.RingTheory.Polynomial.Cyclotomic.Basic
import Mathlib.RingTheory.Polynomial.Cyclotomic.Expand
import InfoGeometry.Canonical.TwelveFoldMasterCharpoly

open scoped Matrix

namespace InfoGeometry.Canonical.TwelveFoldCyclotomicBridge

open Polynomial
open InfoGeometry.Canonical.TwelveFoldExplicitOperators

noncomputable section

theorem cyclotomic12_eq_comp_cyclotomic6 :
    cyclotomic 12 ℂ = (cyclotomic 6 ℂ).comp (X ^ 2) := by
  have h : 12 = 6 * 2 := by norm_num
  rw [h, ← cyclotomic_expand_eq_cyclotomic Nat.prime_two (by decide) ℂ,
    expand_eq_comp_X_pow]

theorem cyclotomic12_eval_master_eq_cyclotomic6_eval_triality :
    aeval masterTwelve (cyclotomic 12 ℂ) =
      aeval TwoSheetThreeColorWeyl.sixTriality (cyclotomic 6 ℂ) := by
  rw [cyclotomic12_eq_comp_cyclotomic6]
  rw [aeval_comp, aeval_X_pow, masterTwelve_sq]

theorem cyclotomic12_eval_master_kernel_eq_triality :
    LinearMap.ker (Matrix.toLin' (R := ℂ)
      (aeval (masterTwelve : Mat23C) (cyclotomic 12 ℂ))) =
      LinearMap.ker (Matrix.toLin' (R := ℂ)
        (aeval (TwoSheetThreeColorWeyl.sixTriality : Mat23C)
          (cyclotomic 6 ℂ))) := by
  rw [cyclotomic12_eval_master_eq_cyclotomic6_eval_triality]

end
end InfoGeometry.Canonical.TwelveFoldCyclotomicBridge
