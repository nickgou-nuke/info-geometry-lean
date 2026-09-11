import InfoGeometry.Inference.PoissonSinkhornTCSTopological
import InfoGeometry.Algebra.FiniteSpinAlgebra
import InfoGeometry.Inference.RegularizedPoissonDeviance
import InfoGeometry.Inference.PoissonBregmanTopological

/-!
# Topology of the finite Poisson Gibbs layer

This owner records continuity of the finite Gibbs weights in a model parameter
and a nonzero temperature.  The positivity property on the model mean is
kept explicit; no continuity claim is made at a vanishing mean or a zero
temperature.
-/

open scoped BigOperators

namespace InfoGeometry.Inference

variable {Data Theta : Type*} [Fintype Data] [Nonempty Data]
  [TopologicalSpace Theta]

theorem continuous_poissonBregman_mean
    (M : PoissonModel (Data := Data) (Theta := Theta))
    (hmean : ∀ i, Continuous (fun θ => M.mean i θ))
    (i : Data) :
    Continuous (fun p : Theta × NonzeroTemperature =>
      poissonBregman (M.observed i) (M.mean i p.1)) := by
  by_cases hy : M.observed i = 0
  · have hformula :
        (fun p : Theta × NonzeroTemperature =>
          poissonBregman (M.observed i) (M.mean i p.1)) =
        (fun p : Theta × NonzeroTemperature => M.mean i p.1) := by
      funext p
      simp [poissonBregman, hy]
    rw [hformula]
    exact (hmean i).comp continuous_fst
  · have hypos : 0 < M.observed i :=
      lt_of_le_of_ne (M.observed_nonneg i) (Ne.symm hy)
    have hmean' : Continuous (fun p : Theta × NonzeroTemperature =>
        M.mean i p.1) := (hmean i).comp continuous_fst
    have hpair : Continuous (fun p : Theta × NonzeroTemperature =>
        ((⟨M.observed i, hypos⟩ : PositiveReal),
          (⟨M.mean i p.1, M.mean_pos i p.1⟩ : PositiveReal))) := by
      apply Continuous.prodMk continuous_const
      apply Continuous.subtype_mk
      exact hmean'
    exact continuous_poissonBregmanPositive.comp hpair

theorem continuous_poissonDeviance_mean
    (M : PoissonModel (Data := Data) (Theta := Theta))
    (hmean : ∀ i, Continuous (fun θ => M.mean i θ))
    (i : Data) :
    Continuous (fun p : Theta × NonzeroTemperature =>
      poissonDeviance (M.observed i) (M.mean i p.1)) := by
  by_cases hy : M.observed i = 0
  · have hformula :
        (fun p : Theta × NonzeroTemperature =>
          poissonDeviance (M.observed i) (M.mean i p.1)) =
        (fun p : Theta × NonzeroTemperature =>
          2 * M.mean i p.1) := by
      funext p
      simp [poissonDeviance, poissonBregman, hy]
    rw [hformula]
    exact continuous_const.mul ((hmean i).comp continuous_fst)
  · have hypos : 0 < M.observed i :=
      lt_of_le_of_ne (M.observed_nonneg i) (Ne.symm hy)
    have hyne : M.observed i ≠ 0 := hy
    have hmean' : Continuous (fun p : Theta × NonzeroTemperature =>
        M.mean i p.1) := (hmean i).comp continuous_fst
    have hratio : Continuous (fun p : Theta × NonzeroTemperature =>
        M.observed i / M.mean i p.1) := by
      exact continuous_const.div hmean' (fun p => (M.mean_pos i p.1).ne')
    have hlog : Continuous (fun p : Theta × NonzeroTemperature =>
        Real.log (M.observed i / M.mean i p.1)) := by
      exact hratio.log (fun p => div_ne_zero hyne (M.mean_pos i p.1).ne')
    have hformula :
        (fun p : Theta × NonzeroTemperature =>
          poissonDeviance (M.observed i) (M.mean i p.1)) =
        (fun p : Theta × NonzeroTemperature =>
          2 * (M.observed i * Real.log
            (M.observed i / M.mean i p.1) -
              (M.observed i - M.mean i p.1))) := by
      funext p
      unfold poissonDeviance poissonBregman
      rw [if_neg hy]
    rw [hformula]
    exact continuous_const.mul
      ((continuous_const.mul hlog).sub
        (continuous_const.sub hmean'))

theorem continuous_poissonWeight
    (M : PoissonModel (Data := Data) (Theta := Theta))
    (hmean : ∀ i, Continuous (fun θ => M.mean i θ))
    (i : Data) :
    Continuous (fun p : Theta × NonzeroTemperature =>
      poissonWeight M p.1 p.2.1 i) := by
  unfold poissonWeight FiniteGibbs.weight
  have henergy (j : Data) : Continuous (fun p : Theta × NonzeroTemperature =>
      M.energy j p.1) := by
    simpa [PoissonModel.energy] using continuous_poissonBregman_mean M hmean j
  have hnum : Continuous (fun p : Theta × NonzeroTemperature =>
      Real.exp (-M.energy i p.1 / p.2.1)) := by
    apply Real.continuous_exp.comp
    exact (henergy i).neg.div
      (continuous_subtype_val.comp continuous_snd)
      (fun p => p.2.property)
  have hden : Continuous (fun p : Theta × NonzeroTemperature =>
      ∑ j : Data, Real.exp (-M.energy j p.1 / p.2.1)) := by
    apply continuous_finset_sum
    intro j hj
    apply Real.continuous_exp.comp
    exact (henergy j).neg.div
      (continuous_subtype_val.comp continuous_snd)
      (fun p => p.2.property)
  have hden_ne : ∀ p : Theta × NonzeroTemperature,
      (∑ j : Data, Real.exp (-M.energy j p.1 / p.2.1)) ≠ 0 := by
    intro p
    exact (FiniteGibbs.partitionFunction_pos M.gibbsModel p.1 p.2.1).ne'
  exact hnum.div hden hden_ne

theorem continuous_poissonPartitionFunction
    (M : PoissonModel (Data := Data) (Theta := Theta))
    (hmean : ∀ i, Continuous (fun θ => M.mean i θ)) :
    Continuous (fun p : Theta × NonzeroTemperature =>
      FiniteGibbs.partitionFunction M.gibbsModel p.1 p.2.1) := by
  unfold FiniteGibbs.partitionFunction
  apply continuous_finset_sum
  intro i hi
  have henergy : Continuous (fun p : Theta × NonzeroTemperature =>
      M.energy i p.1) := by
    simpa [PoissonModel.energy] using continuous_poissonBregman_mean M hmean i
  apply Real.continuous_exp.comp
  exact (henergy.neg).div
    (continuous_subtype_val.comp continuous_snd)
    (fun p => p.2.property)

theorem continuous_poissonFreeEnergy
    (M : PoissonModel (Data := Data) (Theta := Theta))
    (hmean : ∀ i, Continuous (fun θ => M.mean i θ)) :
    Continuous (fun p : Theta × NonzeroTemperature =>
      FiniteGibbs.freeEnergy M.gibbsModel p.1 p.2.1) := by
  unfold FiniteGibbs.freeEnergy
  have hpart := continuous_poissonPartitionFunction M hmean
  have hlog : Continuous (fun p : Theta × NonzeroTemperature =>
      Real.log (FiniteGibbs.partitionFunction M.gibbsModel p.1 p.2.1)) := by
    exact hpart.log (fun p =>
      (FiniteGibbs.partitionFunction_pos M.gibbsModel p.1 p.2.1).ne')
  exact (continuous_subtype_val.comp continuous_snd).neg.mul hlog

theorem poissonFreeEnergy_sublevel_isClosed
    (M : PoissonModel (Data := Data) (Theta := Theta))
    (hmean : ∀ i, Continuous (fun θ => M.mean i θ)) (c : ℝ) :
    IsClosed {p : Theta × NonzeroTemperature |
      FiniteGibbs.freeEnergy M.gibbsModel p.1 p.2.1 ≤ c} := by
  change IsClosed ((fun p : Theta × NonzeroTemperature =>
    FiniteGibbs.freeEnergy M.gibbsModel p.1 p.2.1) ⁻¹' Set.Iic c)
  exact isClosed_Iic.preimage (continuous_poissonFreeEnergy M hmean)

theorem poissonFreeEnergy_levelSet_isClosed
    (M : PoissonModel (Data := Data) (Theta := Theta))
    (hmean : ∀ i, Continuous (fun θ => M.mean i θ)) (c : ℝ) :
    IsClosed {p : Theta × NonzeroTemperature |
      FiniteGibbs.freeEnergy M.gibbsModel p.1 p.2.1 = c} := by
  change IsClosed ((fun p : Theta × NonzeroTemperature =>
    FiniteGibbs.freeEnergy M.gibbsModel p.1 p.2.1) ⁻¹' ({c} : Set ℝ))
  exact isClosed_singleton.preimage (continuous_poissonFreeEnergy M hmean)

theorem exists_poissonFreeEnergy_minimum
    [CompactSpace Theta] [Nonempty Theta]
    (M : PoissonModel (Data := Data) (Theta := Theta))
    (hmean : ∀ i, Continuous (fun θ => M.mean i θ))
    (ε : NonzeroTemperature) :
    ∃ θ : Theta, ∀ θ' : Theta,
      FiniteGibbs.freeEnergy M.gibbsModel θ ε.1 ≤
        FiniteGibbs.freeEnergy M.gibbsModel θ' ε.1 := by
  classical
  have hf : Continuous (fun θ : Theta =>
      FiniteGibbs.freeEnergy M.gibbsModel θ ε.1) := by
    exact (continuous_poissonFreeEnergy M hmean).comp
      (continuous_id.prodMk continuous_const)
  rcases (isCompact_univ : IsCompact (Set.univ : Set Theta)).exists_isMinOn
      Set.univ_nonempty hf.continuousOn with ⟨θ, hθ, hmin⟩
  refine ⟨θ, ?_⟩
  intro θ'
  exact hmin (Set.mem_univ θ')

theorem continuous_poissonWeights
    (M : PoissonModel (Data := Data) (Theta := Theta))
    (hmean : ∀ i, Continuous (fun θ => M.mean i θ)) :
    Continuous (fun p : Theta × NonzeroTemperature =>
      fun i => poissonWeight M p.1 p.2.1 i) := by
  exact continuous_pi (fun i => continuous_poissonWeight M hmean i)

theorem poissonWeight_fiber_isClosed
    (M : PoissonModel (Data := Data) (Theta := Theta))
    (hmean : ∀ i, Continuous (fun θ => M.mean i θ))
    (i : Data) (c : ℝ) :
    IsClosed {p : Theta × NonzeroTemperature |
      poissonWeight M p.1 p.2.1 i = c} := by
  change IsClosed
    ((fun p : Theta × NonzeroTemperature =>
      poissonWeight M p.1 p.2.1 i) ⁻¹' ({c} : Set ℝ))
  exact isClosed_singleton.preimage (continuous_poissonWeight M hmean i)

theorem poissonWeights_continuous_sum_one
    (M : PoissonModel (Data := Data) (Theta := Theta))
    (p : Theta × NonzeroTemperature) :
    ∑ i : Data, (fun q => fun j => poissonWeight M q.1 q.2.1 j) p i = 1 := by
  simpa using poissonWeights_sum_one M p.1 p.2.1

end InfoGeometry.Inference
