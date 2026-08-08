import InfoGeometry.Canonical.PrimeHurwitzLimit

/-!
# Lee--Yang root limits

The closed-set part of the Lee--Yang/Hurwitz passage does not require an
analytic property structure.  Once roots of finite approximants are supplied
and converge, closedness of the unit circle puts the limiting root on the
circle.  The genuinely analytic Hurwitz step is the preceding existence of
such nearby roots.
-/

noncomputable section

namespace InfoGeometry.Analysis.LeeYangRootLimit

open InfoGeometry.Canonical.PrimeHurwitzLimit

/-- The repository's norm-square circle predicate implies unit norm. -/
theorem norm_eq_one_of_onUnitCircle
    {z : ℂ}
    (hz : OnUnitCircle z) :
    ‖z‖ = 1 := by
  rw [OnUnitCircle, Complex.normSq_eq_norm_sq] at hz
  nlinarith [norm_nonneg z]

/-- Unit-circle membership is closed under sequential limits. -/
theorem onUnitCircle_of_tendsto
    (z : ℕ → ℂ)
    (z₀ : ℂ)
    (hz : ∀ n, OnUnitCircle (z n))
    (hlim : Filter.Tendsto z Filter.atTop (nhds z₀)) :
    OnUnitCircle z₀ := by
  have hmem : ∀ n, z n ∈ Metric.sphere (0 : ℂ) 1 := by
    intro n
    simpa [Metric.mem_sphere, dist_zero_right] using
      norm_eq_one_of_onUnitCircle (hz n)
  have hz₀ : z₀ ∈ Metric.sphere (0 : ℂ) 1 :=
    Metric.isClosed_sphere.mem_of_tendsto hlim (Filter.Eventually.of_forall hmem)
  rw [OnUnitCircle, Complex.normSq_eq_norm_sq]
  have hnorm : ‖z₀‖ = 1 := by
    simpa [Metric.mem_sphere, dist_zero_right] using hz₀
  rw [hnorm]
  norm_num

/--
A limit of actual zeros of Lee--Yang approximants lies on the unit circle.

This is the native filtered-stage root-limit theorem.  It assumes the root
family produced by the analytic Hurwitz argument instead of storing the final
circle conclusion in an evidence field.
-/
theorem approximant_root_limit_onUnitCircle
    (A : LeeYangApproximants)
    (root : ℕ → ℂ)
    (z₀ : ℂ)
    (hroot : ∀ n, A.renormZ n (root n) = 0)
    (hlim : Filter.Tendsto root Filter.atTop (nhds z₀)) :
    OnUnitCircle z₀ := by
  apply onUnitCircle_of_tendsto root z₀
  · intro n
    exact A.renormZ_lee_yang n (root n) (hroot n)
  · exact hlim

/--
Zero predicates map to the Lee--Yang circle when each limiting zero is
realized by a convergent family of finite-stage roots.
-/
theorem zeroPredicate_maps_to_unitCircle_of_root_limit
    (XiZero : ℂ → Prop)
    (A : LeeYangApproximants)
    (root : ℂ → ℕ → ℂ)
    (hroot :
      ∀ s, XiZero s → ∀ n, A.renormZ n (root s n) = 0)
    (hlim :
      ∀ s, XiZero s →
        Filter.Tendsto (root s) Filter.atTop (nhds (cayley s)))
    (s : ℂ)
    (hs : XiZero s) :
    OnUnitCircle (cayley s) :=
  approximant_root_limit_onUnitCircle A (root s) (cayley s)
    (hroot s hs) (hlim s hs)

end InfoGeometry.Analysis.LeeYangRootLimit

