import InfoGeometry.Canonical.PoissonGibbsKANModuliTopological
import InfoGeometry.Algebra.FiniteSpinAlgebra

/-!
# Quotient-level Poisson Gibbs probability readout

An unordered family of experts has a canonical probability readout obtained
by averaging the normalized finite Gibbs vectors.  The nonzero-cardinality
property is explicit because the average divides by `K`.
-/

open scoped BigOperators

namespace InfoGeometry.Canonical.KANModuli

open InfoGeometry.Inference

variable {Data Theta : Type*} [Fintype Data] [Nonempty Data]
  [TopologicalSpace Theta]

noncomputable def averagePoissonWeight {K : ℕ} [NeZero K]
    (M : PoissonModel (Data := Data) (Theta := Theta))
    (ε : NonzeroTemperature) (i : Data) :
    ExpertVector Theta K → ℝ :=
  fun v => (∑ k : Fin K, poissonWeight M (v k) ε.1 i) / (K : ℝ)

theorem averagePoissonWeight_smul {K : ℕ} [NeZero K]
    (M : PoissonModel (Data := Data) (Theta := Theta))
    (ε : NonzeroTemperature) (i : Data)
    (σ : Equiv.Perm (Fin K)) (v : ExpertVector Theta K) :
    averagePoissonWeight M ε i (σ • v) =
      averagePoissonWeight M ε i v := by
  unfold averagePoissonWeight
  congr 1
  change (∑ k : Fin K, poissonWeight M (v (σ.symm k)) ε.1 i) = _
  simpa using
    (Fintype.sum_equiv σ.symm
      (fun k : Fin K => poissonWeight M (v (σ.symm k)) ε.1 i)
      (fun k : Fin K => poissonWeight M (v k) ε.1 i)
      (fun _ => rfl))

theorem continuous_averagePoissonWeight {K : ℕ} [NeZero K]
    (M : PoissonModel (Data := Data) (Theta := Theta))
    (hmean : ∀ i, Continuous (fun θ => M.mean i θ))
    (ε : NonzeroTemperature) (i : Data) :
    Continuous (averagePoissonWeight (K := K) M ε i) := by
  unfold averagePoissonWeight
  have hsum : Continuous (fun v : ExpertVector Theta K =>
      ∑ k : Fin K, poissonWeight M (v k) ε.1 i) := by
    have hfixed : Continuous (fun θ : Theta =>
        poissonWeight M θ ε.1 i) := by
      exact (continuous_poissonWeight M hmean i).comp
        (continuous_id.prodMk continuous_const)
    apply continuous_finset_sum
    intro k hk
    exact hfixed.comp (continuous_apply k)
  have hK : (K : ℝ) ≠ 0 := by
    exact_mod_cast (NeZero.ne K : K ≠ 0)
  exact hsum.div continuous_const (fun _ => hK)

noncomputable def averagePoissonWeightOnModuli {K : ℕ} [NeZero K]
    (M : PoissonModel (Data := Data) (Theta := Theta))
    (ε : NonzeroTemperature) (i : Data) :
    KANModuliSpace Theta K → ℝ :=
  sinkhornRoutingLossOnModuli
    (averagePoissonWeight M ε i) (averagePoissonWeight_smul M ε i)

theorem continuous_averagePoissonWeightOnModuli {K : ℕ} [NeZero K]
    (M : PoissonModel (Data := Data) (Theta := Theta))
    (hmean : ∀ i, Continuous (fun θ => M.mean i θ))
    (ε : NonzeroTemperature) (i : Data) :
    Continuous (averagePoissonWeightOnModuli (K := K) M ε i) := by
  exact continuous_sinkhornRoutingLossOnModuli
    (averagePoissonWeight (K := K) M ε i)
    (continuous_averagePoissonWeight (K := K) M hmean ε i)
    (averagePoissonWeight_smul (K := K) M ε i)

@[simp] theorem averagePoissonWeightOnModuli_quotientMap {K : ℕ} [NeZero K]
    (M : PoissonModel (Data := Data) (Theta := Theta))
    (ε : NonzeroTemperature) (i : Data) (v : ExpertVector Theta K) :
    averagePoissonWeightOnModuli M ε i
      (quotientMap (V := Theta) (K := K) v) =
      averagePoissonWeight M ε i v := by
  exact sinkhornRoutingLossOnModuli_quotientMap
    (averagePoissonWeight M ε i)
    (averagePoissonWeight_smul M ε i) v

theorem averagePoissonWeight_sum_one {K : ℕ} [NeZero K]
    (M : PoissonModel (Data := Data) (Theta := Theta))
    (ε : NonzeroTemperature) (v : ExpertVector Theta K) :
    ∑ i : Data, averagePoissonWeight M ε i v = 1 := by
  classical
  unfold averagePoissonWeight
  rw [← Finset.sum_div]
  rw [← Finset.sum_comm]
  simp only [poissonWeights_sum_one]
  simp

theorem averagePoissonWeightOnModuli_fiber_isClosed {K : ℕ} [NeZero K]
    (M : PoissonModel (Data := Data) (Theta := Theta))
    (hmean : ∀ i, Continuous (fun θ => M.mean i θ))
    (ε : NonzeroTemperature) (i : Data) (c : ℝ) :
    IsClosed {q : KANModuliSpace Theta K |
      averagePoissonWeightOnModuli M ε i q = c} := by
  change IsClosed
    ((averagePoissonWeightOnModuli M ε i) ⁻¹' ({c} : Set ℝ))
  exact isClosed_singleton.preimage
    (continuous_averagePoissonWeightOnModuli M hmean ε i)

end InfoGeometry.Canonical.KANModuli
