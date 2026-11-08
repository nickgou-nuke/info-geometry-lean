import Mathlib.Algebra.Order.Floor.Semiring
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Topology.Order.LiminfLimsup
import Mathlib.Tactic
import Omega.Conclusion.PrimeRegisterFiberCdimDensity

namespace Omega.Conclusion

open Filter
open scoped Topology

/-- Paper label: `prop:conclusion-prime-register-fiber-cdim-realize-any-alpha`.
For every target density `α ∈ [0, 1]`, the staircase sequence `⌈α n⌉` realizes that density; the
existing density-to-cdim wrapper then identifies both normalized half-circle dimensions with `α`.
-/
theorem paper_conclusion_prime_register_fiber_cdim_realize_any_alpha (α : ℝ) (hα0 : 0 ≤ α)
    (_hα1 : α ≤ 1) :
    ∃ s : ℕ → ℕ, Tendsto (primeFiberDensitySeq s) Filter.atTop (nhds α) ∧
      primeFiberUpperCdim s = α ∧ primeFiberLowerCdim s = α := by
  let s : ℕ → ℕ := fun n => Nat.ceil (α * n)
  have hshift_nat : Tendsto (fun n : ℕ => n + 1) atTop atTop :=
    tendsto_add_atTop_nat 1
  have hshift : Tendsto (fun n : ℕ => ((n + 1 : ℕ) : ℝ)) atTop atTop :=
    tendsto_natCast_atTop_atTop.comp hshift_nat
  have hρ : Tendsto (primeFiberDensitySeq s) atTop (nhds α) := by
    have h_comp := (tendsto_nat_ceil_mul_div_atTop (R := ℝ) (a := α) hα0).comp hshift
    refine Filter.Tendsto.congr' ?_ h_comp
    filter_upwards with n
    simp [primeFiberDensitySeq, s]
  have hbound : ∀ n, |(s (n + 1) : ℝ) - s (n + 1)| ≤ (0 : ℝ) := by
    intro n
    simp [s]
  have hpackage :=
    paper_conclusion_prime_register_fiber_cdim_density s s α 0 hbound hρ
  rcases hpackage with ⟨_, _, hcdim, _⟩
  have hupper : primeFiberUpperCdim s = α := by
    simpa [primeFiberUpperCdim] using hcdim.limsup_eq
  have hlower : primeFiberLowerCdim s = α := by
    simpa [primeFiberLowerCdim] using hcdim.liminf_eq
  refine ⟨s, hρ, hupper, hlower⟩

end Omega.Conclusion
