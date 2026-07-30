import Mathlib
import Omega.SPG.GodelPrimeDensityHolographyCLT

namespace Omega.SPG

noncomputable section

/-- Log-scale exponent certificate for the ratio of two prime-density holography profiles. -/
def spgGodelPrimeRatioExponent (x y n : Nat) : ℝ :=
  (n : ℝ) * (Real.log (x : ℝ) - Real.log (y : ℝ))

theorem paper_spg_godel_prime_ratio_density :
  (∀ x y n : Nat, 1 ≤ x → 1 ≤ y →
      Real.log (((x : ℝ) / y) ^ (n : ℝ)) = spgGodelPrimeRatioExponent x y n) ∧
  (∀ x n : Nat, 1 ≤ x → spgGodelPrimeRatioExponent x x n = 0) := by
  refine ⟨?_, ?_⟩
  · intro x y n hx hy
    unfold spgGodelPrimeRatioExponent
    have hx' : 0 < (x : ℝ) := by exact_mod_cast hx
    have hy' : 0 < (y : ℝ) := by exact_mod_cast hy
    have hdiv : 0 < (x : ℝ) / y := by exact div_pos hx' hy'
    rw [Real.log_rpow hdiv]
    rw [Real.log_div (show (x : ℝ) ≠ 0 by positivity) (show (y : ℝ) ≠ 0 by positivity)]
  · intro x n hx
    unfold spgGodelPrimeRatioExponent
    ring_nf

end
end Omega.SPG
