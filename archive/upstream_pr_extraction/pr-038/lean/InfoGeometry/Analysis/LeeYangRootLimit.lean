import InfoGeometry.Canonical.PrimeHurwitzLimit

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

theorem onUnitCircle_iff_norm_eq_one {z : ℂ} :
    OnUnitCircle z ↔ ‖z‖ = 1 := by
  constructor
  · exact norm_eq_one_of_onUnitCircle
  · intro hz
    rw [OnUnitCircle, Complex.normSq_eq_norm_sq, hz]
    norm_num

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

/-- A convergent family of filtered-stage roots has a unit-circle limit. -/
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

/-- A supplied zero predicate maps to the unit circle when each selected point
is realized by a convergent family of finite-stage roots. -/
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
