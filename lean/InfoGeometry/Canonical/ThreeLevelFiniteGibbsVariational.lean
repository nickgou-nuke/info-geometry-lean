import InfoGeometry.Canonical.ThreeLevelFiniteGibbsWeights
import InfoGeometry.Canonical.ThreeLevelFiniteGibbsFreeEnergy
import InfoGeometry.Inference.GibbsVariationalDecomposition
import InfoGeometry.Inference.FiniteRelativeEntropyEquality

open scoped BigOperators

namespace InfoGeometry.Canonical

namespace ThreeLevelFiniteGibbs

open InfoGeometry.Inference
open InfoGeometry.Inference.FiniteGibbs

variable {SuperSector Sector : Type*}
  [Fintype SuperSector] [Nonempty SuperSector]
  [Fintype Sector] [Nonempty Sector] [DecidableEq SuperSector]
variable (State : Sector → Type*)
variable [∀ s, Fintype (State s)] [∀ s, Nonempty (State s)]

/-- The outer super-sector model as a finite Gibbs model. -/
noncomputable def superModel
    (super : Sector → SuperSector)
    (energy : ∀ s, State s → ℝ) (particleNumber : Sector → ℝ)
    (superNumber : SuperSector → ℝ)
    (β μ ν : ℝ) :
    FiniteGibbs.Model (Data := SuperSector) (Theta := Unit) :=
  fun g _ => effectiveSuperPotential State super energy particleNumber superNumber β μ ν g

/-- The super-model partition at temperature `1 / β` is the grand partition. -/
theorem superModel_partition_eq_grandPartition
    (super : Sector → SuperSector)
    (energy : ∀ s, State s → ℝ) (particleNumber : Sector → ℝ)
    (superNumber : SuperSector → ℝ)
    (β μ ν : ℝ) (hβ : β ≠ 0)
    (fiber_nonempty : ∀ g, (superFiber super g).Nonempty) :
    partitionFunction (superModel State super energy particleNumber superNumber β μ ν) () (1 / β) =
      grandPartition State super energy particleNumber superNumber β μ ν := by
  classical
  unfold partitionFunction superModel
  apply Finset.sum_congr rfl
  intro g hg
  rw [show -effectiveSuperPotential State super energy particleNumber superNumber β μ ν g / (1 / β) =
      -β * effectiveSuperPotential State super energy particleNumber superNumber β μ ν g by
        field_simp [hβ]]
  exact exp_neg_beta_mul_effectiveSuperPotential_eq_outerNumerator
    State super energy particleNumber superNumber β μ ν hβ fiber_nonempty g

/-- The super-model Gibbs weight is the outer super-sector weight. -/
theorem superModel_weight_eq_outerWeight
    (super : Sector → SuperSector)
    (energy : ∀ s, State s → ℝ) (particleNumber : Sector → ℝ)
    (superNumber : SuperSector → ℝ)
    (β μ ν : ℝ) (hβ : β ≠ 0)
    (fiber_nonempty : ∀ g, (superFiber super g).Nonempty) (g : SuperSector) :
    weight (superModel State super energy particleNumber superNumber β μ ν) () (1 / β) g =
      outerWeight State super energy particleNumber superNumber β μ ν g := by
  change Real.exp (-effectiveSuperPotential State super energy particleNumber superNumber β μ ν g /
      (1 / β)) /
      partitionFunction (superModel State super energy particleNumber superNumber β μ ν) () (1 / β) =
    outerNumerator State super energy particleNumber superNumber β μ ν g /
      grandPartition State super energy particleNumber superNumber β μ ν
  rw [superModel_partition_eq_grandPartition State super energy particleNumber superNumber β μ ν
    hβ fiber_nonempty]
  rw [show -effectiveSuperPotential State super energy particleNumber superNumber β μ ν g / (1 / β) =
      -β * effectiveSuperPotential State super energy particleNumber superNumber β μ ν g by
        field_simp [hβ]]
  rw [exp_neg_beta_mul_effectiveSuperPotential_eq_outerNumerator
    State super energy particleNumber superNumber β μ ν hβ fiber_nonempty g]

/-- Entropy-regularized outer objective at inverse temperature `β`. -/
noncomputable def outerVariationalObjective
    (super : Sector → SuperSector)
    (energy : ∀ s, State s → ℝ) (particleNumber : Sector → ℝ)
    (superNumber : SuperSector → ℝ)
    (β μ ν : ℝ) (q : SuperSector → ℝ) : ℝ :=
  ∑ g, q g * effectiveSuperPotential State super energy particleNumber superNumber β μ ν g +
    (1 / β) * ∑ g, q g * Real.log (q g)

/-- The outer variational objective equals the grand free energy plus a KL gap. -/
theorem outerVariationalObjective_eq_grandFreeEnergy_add_relativeEntropy
    (super : Sector → SuperSector)
    (energy : ∀ s, State s → ℝ) (particleNumber : Sector → ℝ)
    (superNumber : SuperSector → ℝ)
    {β μ ν : ℝ} (hβ : 0 < β) (q : SuperSector → ℝ)
    (hq_pos : ∀ g, 0 < q g) (hq_sum : ∑ g, q g = 1)
    (fiber_nonempty : ∀ g, (superFiber super g).Nonempty) :
    outerVariationalObjective State super energy particleNumber superNumber β μ ν q =
      grandFreeEnergy State super energy particleNumber superNumber β μ ν +
        (1 / β) * finiteRelativeEntropy q
          (outerWeight State super energy particleNumber superNumber β μ ν) := by
  have hβne : β ≠ 0 := ne_of_gt hβ
  have hε : 0 < (1 / β) := one_div_pos.mpr hβ
  have hgeneric :=
    entropyRegularizedObjective_eq_freeEnergy_add_relativeEntropy
      (superModel State super energy particleNumber superNumber β μ ν) () hε
      q hq_pos hq_sum
  calc
    outerVariationalObjective State super energy particleNumber superNumber β μ ν q =
        entropyRegularizedObjective
          (superModel State super energy particleNumber superNumber β μ ν) () (1 / β) q := rfl
    _ = freeEnergy (superModel State super energy particleNumber superNumber β μ ν) () (1 / β) +
        (1 / β) * finiteRelativeEntropy q
          (weight (superModel State super energy particleNumber superNumber β μ ν) () (1 / β)) := hgeneric
    _ = grandFreeEnergy State super energy particleNumber superNumber β μ ν +
        (1 / β) * finiteRelativeEntropy q
          (outerWeight State super energy particleNumber superNumber β μ ν) := by
      rw [show freeEnergy (superModel State super energy particleNumber superNumber β μ ν) ()
          (1 / β) = grandFreeEnergy State super energy particleNumber superNumber β μ ν by
            unfold freeEnergy grandFreeEnergy
            rw [superModel_partition_eq_grandPartition
              State super energy particleNumber superNumber β μ ν hβne fiber_nonempty]]
      apply congrArg (fun p => grandFreeEnergy State super energy particleNumber superNumber β μ ν +
        (1 / β) * finiteRelativeEntropy q p)
      funext g
      exact superModel_weight_eq_outerWeight
        State super energy particleNumber superNumber β μ ν hβne fiber_nonempty g

/-- The KL term in the outer variational certificate is nonnegative. -/
theorem outerVariationalGap_nonneg
    (super : Sector → SuperSector)
    (energy : ∀ s, State s → ℝ) (particleNumber : Sector → ℝ)
    (superNumber : SuperSector → ℝ)
    {β μ ν : ℝ} (hβ : 0 < β) (q : SuperSector → ℝ)
    (hq_pos : ∀ g, 0 < q g) (hq_sum : ∑ g, q g = 1)
    (fiber_nonempty : ∀ g, (superFiber super g).Nonempty) :
    0 ≤ (1 / β) * finiteRelativeEntropy q
      (outerWeight State super energy particleNumber superNumber β μ ν) := by
  exact mul_nonneg (le_of_lt (one_div_pos.mpr hβ))
    (finiteRelativeEntropy_nonneg q
      (outerWeight State super energy particleNumber superNumber β μ ν)
      hq_pos
      (fun g => by
        unfold outerWeight outerNumerator
        exact div_pos
          (mul_pos (Real.exp_pos _) (superPartition_pos State super energy particleNumber β μ
            fiber_nonempty g))
          (grandPartition_pos State super energy particleNumber superNumber β μ ν
            fiber_nonempty))
      hq_sum
      (sum_outerWeight_eq_one State super energy particleNumber superNumber β μ ν
        fiber_nonempty))

/-- The outer Gibbs distribution minimizes the entropy-regularized objective. -/
theorem grandFreeEnergy_le_outerVariationalObjective
    (super : Sector → SuperSector)
    (energy : ∀ s, State s → ℝ) (particleNumber : Sector → ℝ)
    (superNumber : SuperSector → ℝ)
    {β μ ν : ℝ} (hβ : 0 < β) (q : SuperSector → ℝ)
    (hq_pos : ∀ g, 0 < q g) (hq_sum : ∑ g, q g = 1)
    (fiber_nonempty : ∀ g, (superFiber super g).Nonempty) :
    grandFreeEnergy State super energy particleNumber superNumber β μ ν ≤
      outerVariationalObjective State super energy particleNumber superNumber β μ ν q := by
  rw [outerVariationalObjective_eq_grandFreeEnergy_add_relativeEntropy
    State super energy particleNumber superNumber hβ q hq_pos hq_sum fiber_nonempty]
  exact le_add_of_nonneg_right
    (outerVariationalGap_nonneg State super energy particleNumber superNumber hβ q hq_pos
      hq_sum fiber_nonempty)

/-- Equality in the outer variational bound characterizes the outer Gibbs
    distribution among positive normalized super-sector weights. -/
theorem outerVariationalObjective_eq_grandFreeEnergy_iff
    (super : Sector → SuperSector)
    (energy : ∀ s, State s → ℝ) (particleNumber : Sector → ℝ)
    (superNumber : SuperSector → ℝ)
    {β μ ν : ℝ} (hβ : 0 < β) (q : SuperSector → ℝ)
    (hq_pos : ∀ g, 0 < q g) (hq_sum : ∑ g, q g = 1)
    (fiber_nonempty : ∀ g, (superFiber super g).Nonempty) :
    outerVariationalObjective State super energy particleNumber superNumber β μ ν q =
      grandFreeEnergy State super energy particleNumber superNumber β μ ν ↔
      q = outerWeight State super energy particleNumber superNumber β μ ν := by
  rw [outerVariationalObjective_eq_grandFreeEnergy_add_relativeEntropy
    State super energy particleNumber superNumber hβ q hq_pos hq_sum fiber_nonempty]
  have hfactor : (1 / β) ≠ 0 := ne_of_gt (one_div_pos.mpr hβ)
  have hp_pos : ∀ g, 0 < outerWeight State super energy particleNumber superNumber β μ ν g := by
    intro g
    unfold outerWeight outerNumerator
    exact div_pos
      (mul_pos (Real.exp_pos _) (superPartition_pos State super energy particleNumber β μ
        fiber_nonempty g))
      (grandPartition_pos State super energy particleNumber superNumber β μ ν
        fiber_nonempty)
  have hp_sum : ∑ g, outerWeight State super energy particleNumber superNumber β μ ν g = 1 :=
    sum_outerWeight_eq_one State super energy particleNumber superNumber β μ ν fiber_nonempty
  constructor
  · intro h
    have hgap : (1 / β) * finiteRelativeEntropy q
        (outerWeight State super energy particleNumber superNumber β μ ν) = 0 := by
      linarith
    have hkl : finiteRelativeEntropy q
        (outerWeight State super energy particleNumber superNumber β μ ν) = 0 :=
      (mul_eq_zero.mp hgap).resolve_left hfactor
    exact (finiteRelativeEntropy_eq_zero_iff q
      (outerWeight State super energy particleNumber superNumber β μ ν)
      hq_pos hp_pos hq_sum hp_sum).mp hkl
  · intro hq
    have hkl : finiteRelativeEntropy q
        (outerWeight State super energy particleNumber superNumber β μ ν) = 0 := by
      apply (finiteRelativeEntropy_eq_zero_iff q
        (outerWeight State super energy particleNumber superNumber β μ ν)
        hq_pos hp_pos hq_sum hp_sum).mpr
      exact hq
    rw [hkl]
    ring

end ThreeLevelFiniteGibbs

end InfoGeometry.Canonical
