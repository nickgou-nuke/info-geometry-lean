import InfoGeometry.Canonical.KANModuliSinkhornContinuity
import InfoGeometry.Algebra.FiniteSpinAlgebra
import InfoGeometry.Canonical.KANModuliCompact
import InfoGeometry.Inference.PoissonGibbsTopological

/-!
# Poisson Gibbs free energy on the KAN permutation quotient

The finite Gibbs free energy is aggregated across a finite family of experts.
Its descent is conditional on the explicit permutation symmetry of that finite
sum, so the quotient construction does not hide an unproved gauge law.
-/

open scoped BigOperators

namespace InfoGeometry.Canonical.KANModuli

open InfoGeometry.Inference

variable {Data Theta : Type*} [Fintype Data] [Nonempty Data]
  [TopologicalSpace Theta]

noncomputable def expertPoissonFreeEnergy {K : ℕ}
    (M : PoissonModel (Data := Data) (Theta := Theta))
    (ε : NonzeroTemperature) : ExpertVector Theta K → ℝ :=
  fun v => ∑ k : Fin K,
    FiniteGibbs.freeEnergy M.gibbsModel (v k) ε.1

theorem expertPoissonFreeEnergy_smul {K : ℕ}
    (M : PoissonModel (Data := Data) (Theta := Theta))
    (ε : NonzeroTemperature) (σ : Equiv.Perm (Fin K))
    (v : ExpertVector Theta K) :
    expertPoissonFreeEnergy M ε (σ • v) =
      expertPoissonFreeEnergy M ε v := by
  change (∑ k : Fin K,
      FiniteGibbs.freeEnergy M.gibbsModel (v (σ.symm k)) ε.1) = _
  simpa using
    (Fintype.sum_equiv σ.symm
      (fun k : Fin K => FiniteGibbs.freeEnergy M.gibbsModel (v (σ.symm k)) ε.1)
      (fun k : Fin K => FiniteGibbs.freeEnergy M.gibbsModel (v k) ε.1)
      (fun _ => rfl))

theorem continuous_expertPoissonFreeEnergy {K : ℕ}
    (M : PoissonModel (Data := Data) (Theta := Theta))
    (hmean : ∀ i, Continuous (fun θ => M.mean i θ))
    (ε : NonzeroTemperature) :
    Continuous (expertPoissonFreeEnergy (K := K) M ε) := by
  unfold expertPoissonFreeEnergy
  apply continuous_finset_sum
  intro k hk
  have hfree : Continuous (fun θ : Theta =>
      FiniteGibbs.freeEnergy M.gibbsModel θ ε.1) := by
    exact (continuous_poissonFreeEnergy M hmean).comp
      (continuous_id.prodMk continuous_const)
  exact hfree.comp (continuous_apply k)

noncomputable def expertPoissonFreeEnergyOnModuli {K : ℕ}
    (M : PoissonModel (Data := Data) (Theta := Theta))
    (ε : NonzeroTemperature) : KANModuliSpace Theta K → ℝ :=
  sinkhornRoutingLossOnModuli
    (expertPoissonFreeEnergy (K := K) M ε)
    (expertPoissonFreeEnergy_smul (K := K) M ε)

theorem continuous_expertPoissonFreeEnergyOnModuli {K : ℕ}
    (M : PoissonModel (Data := Data) (Theta := Theta))
    (hmean : ∀ i, Continuous (fun θ => M.mean i θ))
    (ε : NonzeroTemperature) :
    Continuous (expertPoissonFreeEnergyOnModuli (K := K) M ε) := by
  exact continuous_sinkhornRoutingLossOnModuli
    (expertPoissonFreeEnergy (K := K) M ε)
    (continuous_expertPoissonFreeEnergy (K := K) M hmean ε)
    (expertPoissonFreeEnergy_smul (K := K) M ε)

@[simp] theorem expertPoissonFreeEnergyOnModuli_quotientMap {K : ℕ}
    (M : PoissonModel (Data := Data) (Theta := Theta))
    (ε : NonzeroTemperature) (v : ExpertVector Theta K) :
    expertPoissonFreeEnergyOnModuli (K := K) M ε
      (quotientMap (V := Theta) (K := K) v) =
      expertPoissonFreeEnergy (K := K) M ε v := by
  exact sinkhornRoutingLossOnModuli_quotientMap
    (expertPoissonFreeEnergy (K := K) M ε)
    (expertPoissonFreeEnergy_smul (K := K) M ε) v

theorem expertPoissonFreeEnergyOnModuli_sublevel_isClosed {K : ℕ}
    (M : PoissonModel (Data := Data) (Theta := Theta))
    (hmean : ∀ i, Continuous (fun θ => M.mean i θ))
    (ε : NonzeroTemperature) (c : ℝ) :
    IsClosed {q : KANModuliSpace Theta K |
      expertPoissonFreeEnergyOnModuli (K := K) M ε q ≤ c} := by
  change IsClosed
    ((expertPoissonFreeEnergyOnModuli (K := K) M ε) ⁻¹' Set.Iic c)
  exact isClosed_Iic.preimage
    (continuous_expertPoissonFreeEnergyOnModuli (K := K) M hmean ε)

theorem exists_global_minimum_expertPoissonFreeEnergyOnModuli {K : ℕ}
    [CompactSpace Theta] [Nonempty Theta]
    (M : PoissonModel (Data := Data) (Theta := Theta))
    (hmean : ∀ i, Continuous (fun θ => M.mean i θ))
    (ε : NonzeroTemperature) :
    ∃ q : KANModuliSpace Theta K, ∀ q',
      expertPoissonFreeEnergyOnModuli (K := K) M ε q ≤
        expertPoissonFreeEnergyOnModuli (K := K) M ε q' := by
  classical
  have hq : (Set.univ : Set (KANModuliSpace Theta K)).Nonempty := by
    let θ : Theta := Classical.choice (inferInstance : Nonempty Theta)
    let v : ExpertVector Theta K := fun _ => θ
    exact ⟨quotientMap (V := Theta) (K := K) v, Set.mem_univ _⟩
  letI : Nonempty (KANModuliSpace Theta K) := ⟨hq.choose⟩
  rcases (isCompact_univ :
      IsCompact (Set.univ : Set (KANModuliSpace Theta K))).exists_isMinOn
      hq (continuous_expertPoissonFreeEnergyOnModuli (K := K) M hmean ε).continuousOn
      with ⟨q, hq', hmin⟩
  refine ⟨q, ?_⟩
  intro q'
  exact hmin (Set.mem_univ q')

theorem expertPoissonFreeEnergyOnModuli_superlevel_isClosed {K : ℕ}
    (M : PoissonModel (Data := Data) (Theta := Theta))
    (hmean : ∀ i, Continuous (fun θ => M.mean i θ))
    (ε : NonzeroTemperature) (c : ℝ) :
    IsClosed {q : KANModuliSpace Theta K |
      c ≤ expertPoissonFreeEnergyOnModuli (K := K) M ε q} := by
  change IsClosed
    ((expertPoissonFreeEnergyOnModuli (K := K) M ε) ⁻¹' Set.Ici c)
  exact isClosed_Ici.preimage
    (continuous_expertPoissonFreeEnergyOnModuli (K := K) M hmean ε)

theorem expertPoissonFreeEnergyOnModuli_levelSet_isClosed {K : ℕ}
    (M : PoissonModel (Data := Data) (Theta := Theta))
    (hmean : ∀ i, Continuous (fun θ => M.mean i θ))
    (ε : NonzeroTemperature) (c : ℝ) :
    IsClosed {q : KANModuliSpace Theta K |
      expertPoissonFreeEnergyOnModuli (K := K) M ε q = c} := by
  change IsClosed
    ((expertPoissonFreeEnergyOnModuli (K := K) M ε) ⁻¹' ({c} : Set ℝ))
  exact isClosed_singleton.preimage
    (continuous_expertPoissonFreeEnergyOnModuli (K := K) M hmean ε)

theorem expertPoissonFreeEnergyOnModuli_sublevel_isCompact {K : ℕ}
    [CompactSpace Theta]
    (M : PoissonModel (Data := Data) (Theta := Theta))
    (hmean : ∀ i, Continuous (fun θ : Theta => M.mean i θ))
    (ε : NonzeroTemperature) (c : ℝ) :
    IsCompact {q : KANModuliSpace Theta K |
      expertPoissonFreeEnergyOnModuli (K := K) M ε q ≤ c} := by
  exact IsClosed.isCompact
    (expertPoissonFreeEnergyOnModuli_sublevel_isClosed (K := K) M hmean ε c)

theorem expertPoissonFreeEnergyOnModuli_superlevel_isCompact {K : ℕ}
    [CompactSpace Theta]
    (M : PoissonModel (Data := Data) (Theta := Theta))
    (hmean : ∀ i, Continuous (fun θ : Theta => M.mean i θ))
    (ε : NonzeroTemperature) (c : ℝ) :
    IsCompact {q : KANModuliSpace Theta K |
      c ≤ expertPoissonFreeEnergyOnModuli (K := K) M ε q} := by
  exact IsClosed.isCompact
    (expertPoissonFreeEnergyOnModuli_superlevel_isClosed (K := K) M hmean ε c)

theorem expertPoissonFreeEnergyOnModuli_levelSet_isCompact {K : ℕ}
    [CompactSpace Theta]
    (M : PoissonModel (Data := Data) (Theta := Theta))
    (hmean : ∀ i, Continuous (fun θ : Theta => M.mean i θ))
    (ε : NonzeroTemperature) (c : ℝ) :
    IsCompact {q : KANModuliSpace Theta K |
      expertPoissonFreeEnergyOnModuli (K := K) M ε q = c} := by
  exact isCompact_levelSet_on_kanModuli
    (expertPoissonFreeEnergyOnModuli (K := K) M ε)
    (continuous_expertPoissonFreeEnergyOnModuli (K := K) M hmean ε) c

theorem exists_global_maximum_expertPoissonFreeEnergyOnModuli {K : ℕ}
    [CompactSpace Theta] [Nonempty Theta]
    (M : PoissonModel (Data := Data) (Theta := Theta))
    (hmean : ∀ i, Continuous (fun θ => M.mean i θ))
    (ε : NonzeroTemperature) :
    ∃ q : KANModuliSpace Theta K, ∀ q',
      expertPoissonFreeEnergyOnModuli (K := K) M ε q' ≤
        expertPoissonFreeEnergyOnModuli (K := K) M ε q := by
  exact exists_global_maximum_on_kanModuli
    (expertPoissonFreeEnergyOnModuli (K := K) M ε)
    (continuous_expertPoissonFreeEnergyOnModuli (K := K) M hmean ε)

end InfoGeometry.Canonical.KANModuli
