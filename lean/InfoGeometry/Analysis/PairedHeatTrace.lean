import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Topology.Algebra.InfiniteSum.Basic
import Mathlib.Tactic

/-!
# Regulated spectral sums with an explicit pairing

Every infinite sum below has a `HasSum` hypothesis: the totalized `tsum` of
a nonsummable series is never used as a finite heat trace. A bijection of
nonzero modes preserves their energies and cancels their convergent sums.
The zero-mode dimensions remain. This is the spectral-sum step of
McKean--Singer, conditional on the operator's spectral expansion and pairing;
it is not an elliptic heat-kernel construction or a continuum-limit theorem.
-/

noncomputable section

namespace InfoGeometry.Analysis.PairedHeatTrace

open Filter
open scoped Topology BigOperators

theorem paired_hasSum_eq {I J : Type*} (e : I ≃ J)
    {f : I → ℝ} {g : J → ℝ} {a b : ℝ}
    (hf : HasSum f a) (hg : HasSum g b)
    (hpair : ∀ i, g (e i) = f i) : a = b := by
  have he : HasSum (fun i => g (e i)) b := e.hasSum_iff.mpr hg
  have hfun : (fun i => g (e i)) = f := funext hpair
  rw [hfun] at he
  exact hf.unique he

/-- At each positive regulator, the traces differ by the zero-mode count. -/
theorem heat_trace_difference {I J : Type*} (e : I ≃ J)
    (μp : I → ℝ) (μm : J → ℝ) (kp km : ℕ) (t Tp Tm : ℝ)
    (hp : HasSum (fun i => Real.exp (-t * μp i)) (Tp - kp))
    (hm : HasSum (fun j => Real.exp (-t * μm j)) (Tm - km))
    (hpair : ∀ i, μm (e i) = μp i) :
    Tp - Tm = (kp : ℝ) - km := by
  have h := paired_hasSum_eq e hp hm (fun i => by rw [hpair i])
  linarith

/-- The regulator limit is taken after subtracting finite traces. -/
theorem heat_supertrace_tendsto_index {I J : Type*} (e : I ≃ J)
    (μp : I → ℝ) (μm : J → ℝ) (kp km : ℕ) (Tp Tm : ℝ → ℝ)
    (hp : ∀ t > 0, HasSum (fun i => Real.exp (-t * μp i)) (Tp t - kp))
    (hm : ∀ t > 0, HasSum (fun j => Real.exp (-t * μm j)) (Tm t - km))
    (hpair : ∀ i, μm (e i) = μp i) :
    Tendsto (fun t => Tp t - Tm t) (𝓝[>] (0 : ℝ)) (𝓝 ((kp : ℝ) - km)) := by
  apply tendsto_const_nhds.congr'
  filter_upwards [self_mem_nhdsWithin] with t ht
  exact (heat_trace_difference e μp μm kp km t (Tp t) (Tm t)
    (hp t ht) (hm t ht) hpair).symm

/-- The same cancellation is exact at every matched finite cutoff. -/
theorem finite_heat_cutoff_difference {I J : Type*} (e : I ≃ J)
    (s : Finset I) (μp : I → ℝ) (μm : J → ℝ) (kp km : ℕ) (t : ℝ)
    (hpair : ∀ i, μm (e i) = μp i) :
    ((kp : ℝ) + ∑ i ∈ s, Real.exp (-t * μp i)) -
      ((km : ℝ) + ∑ j ∈ s.map e.toEmbedding, Real.exp (-t * μm j)) =
        (kp : ℝ) - km := by
  simp only [Finset.sum_map, Equiv.toEmbedding_apply, hpair]
  ring

end InfoGeometry.Analysis.PairedHeatTrace
