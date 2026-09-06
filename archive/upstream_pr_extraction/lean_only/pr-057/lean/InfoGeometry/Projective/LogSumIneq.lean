
import InfoGeometry.Projective.LogSum

/-!
# Log-sum inequality wrapper alias

Compatibility alias exposing the projective log-sum wrapper.
-/

namespace InfoGeometry.Projective

/-- Compatibility alias for `logSum_inequality`. -/
theorem logSumInequality
    {ι : Type*} (s : Finset ι)
    (a b : ι → ℝ)
    (ha : ∀ i, i ∈ s → 0 < a i)
    (hb : ∀ i, i ∈ s → 0 < b i) :
    (∑ i ∈ s, a i * Real.log (a i / b i))
      ≥
    (∑ i ∈ s, a i) * Real.log ((∑ i ∈ s, a i) / (∑ i ∈ s, b i)) :=
  logSum_inequality (s := s) (a := a) (b := b) ha hb

end InfoGeometry.Projective
