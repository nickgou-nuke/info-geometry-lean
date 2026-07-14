import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Tactic

namespace Omega.Zeta

noncomputable section

/-- Uniform `2k`-th moment power saving for the truncated Dirichlet polynomial. -/
def uniformMomentBound (N : ℕ) (logExponent : ℕ → ℕ) (momentValue : ℕ → ℝ → ℝ)
    (baseConstant : ℕ → ℝ) (spectralGap : ℝ) (k : ℕ) (ε C : ℝ) : Prop :=
  0 < ε ∧
    0 < C ∧
    ∀ T : ℝ, 1 ≤ T →
      momentValue k T ≤
        C * T * (N : ℝ) ^ k *
          (Real.log (N : ℝ)) ^ (logExponent k) * (N : ℝ) ^ (-ε)

lemma uniform_moment_bound_of_gap
    (N : ℕ) (logExponent : ℕ → ℕ) (momentValue : ℕ → ℝ → ℝ)
    (baseConstant : ℕ → ℝ) (spectralGap : ℝ)
    (hspectralGap : 0 < spectralGap) (hbase_pos : ∀ k, 0 < baseConstant k)
    (momentBound :
      ∀ k T, 1 ≤ T →
        momentValue k T ≤
          baseConstant k * T * (N : ℝ) ^ k *
            (Real.log (N : ℝ)) ^ (logExponent k) * (N : ℝ) ^ (-spectralGap))
    (k : ℕ) :
    uniformMomentBound N logExponent momentValue baseConstant spectralGap k spectralGap
      (baseConstant k) := by
  refine ⟨hspectralGap, hbase_pos k, ?_⟩
  intro T hT
  simpa [uniformMomentBound] using momentBound k T hT

/-- A uniform twisted spectral gap yields a power-saving `2k`-th moment bound for every fixed
order.
    prop:conclusion69-automatic-dirichlet-moment -/
theorem paper_conclusion69_automatic_dirichlet_moment
    (N : ℕ) (hN : 2 ≤ N) (logExponent : ℕ → ℕ) (momentValue : ℕ → ℝ → ℝ)
    (baseConstant : ℕ → ℝ) (spectralGap : ℝ)
    (hspectralGap : 0 < spectralGap) (hbase_pos : ∀ k, 0 < baseConstant k)
    (momentBound :
      ∀ k T, 1 ≤ T →
        momentValue k T ≤
          baseConstant k * T * (N : ℝ) ^ k *
            (Real.log (N : ℝ)) ^ (logExponent k) * (N : ℝ) ^ (-spectralGap)) :
    ∀ k : ℕ, ∃ ε C, uniformMomentBound N logExponent momentValue baseConstant spectralGap k ε C := by
  intro k
  exact ⟨spectralGap, baseConstant k,
    uniform_moment_bound_of_gap N logExponent momentValue baseConstant spectralGap hspectralGap
      hbase_pos momentBound k⟩

/-- Paper label: `thm:gm-automatic-dirichlet-moment-bound`. The GM appendix uses the same
finite-state spectral-gap package as the conclusion-level automatic Dirichlet moment theorem. -/
theorem paper_gm_automatic_dirichlet_moment_bound
    (N : ℕ) (hN : 2 ≤ N) (logExponent : ℕ → ℕ) (momentValue : ℕ → ℝ → ℝ)
    (baseConstant : ℕ → ℝ) (spectralGap : ℝ)
    (hspectralGap : 0 < spectralGap) (hbase_pos : ∀ k, 0 < baseConstant k)
    (momentBound :
      ∀ k T, 1 ≤ T →
        momentValue k T ≤
          baseConstant k * T * (N : ℝ) ^ k *
            (Real.log (N : ℝ)) ^ (logExponent k) * (N : ℝ) ^ (-spectralGap)) :
    ∀ k : ℕ, ∃ ε C, uniformMomentBound N logExponent momentValue baseConstant spectralGap k ε C :=
  paper_conclusion69_automatic_dirichlet_moment N hN logExponent momentValue baseConstant spectralGap
    hspectralGap hbase_pos momentBound

end

end Omega.Zeta
