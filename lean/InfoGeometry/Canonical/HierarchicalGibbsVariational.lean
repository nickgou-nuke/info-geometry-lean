import InfoGeometry.Canonical.HierarchicalGibbsFreeEnergy
import InfoGeometry.Inference.GibbsVariationalDecomposition
import InfoGeometry.Inference.FiniteRelativeEntropyEquality

open scoped BigOperators

namespace InfoGeometry.Canonical

namespace HierarchicalGrandCanonical

open InfoGeometry.Inference
open InfoGeometry.Inference.FiniteGibbs

variable {Sector : Type*} [Fintype Sector] [Nonempty Sector]
variable (State : Sector → Type*)
variable [∀ s, Fintype (State s)] [∀ s, Nonempty (State s)]

/-- The outer sector model, viewed as an ordinary finite Gibbs model. -/
noncomputable def sectorModel
    (energy : ∀ s, State s → ℝ) (particleNumber : Sector → ℝ)
    (β μ : ℝ) :
    FiniteGibbs.Model (Data := Sector) (Theta := Unit) :=
  ⟨fun s _ => effectiveSectorPotential State energy particleNumber β μ s⟩

/-- The sector model's partition at temperature `1 / β` is the hierarchical
    grand partition. -/
theorem sectorModel_partition_eq_grandPartition
    (energy : ∀ s, State s → ℝ) (particleNumber : Sector → ℝ)
    (β μ : ℝ) (hβ : β ≠ 0) :
    partitionFunction (sectorModel State energy particleNumber β μ) () (1 / β) =
      grandPartition State energy particleNumber β μ := by
  classical
  unfold partitionFunction sectorModel
  apply Finset.sum_congr rfl
  intro s hs
  rw [show -effectiveSectorPotential State energy particleNumber β μ s / (1 / β) =
      -β * effectiveSectorPotential State energy particleNumber β μ s by
        field_simp [hβ]]
  exact exp_neg_beta_mul_effectiveSectorPotential_eq_sectorNumerator
    State energy particleNumber β μ s hβ

/-- The sector model's Gibbs weight is the hierarchical sector weight. -/
theorem sectorModel_weight_eq_sectorWeight
    (energy : ∀ s, State s → ℝ) (particleNumber : Sector → ℝ)
    (β μ : ℝ) (hβ : β ≠ 0) (s : Sector) :
    weight (sectorModel State energy particleNumber β μ) () (1 / β) s =
      sectorWeight State energy particleNumber β μ s := by
  change Real.exp (-effectiveSectorPotential State energy particleNumber β μ s / (1 / β)) /
      partitionFunction (sectorModel State energy particleNumber β μ) () (1 / β) =
    sectorNumerator State energy particleNumber β μ s /
      grandPartition State energy particleNumber β μ
  rw [sectorModel_partition_eq_grandPartition State energy particleNumber β μ hβ]
  rw [show -effectiveSectorPotential State energy particleNumber β μ s / (1 / β) =
      -β * effectiveSectorPotential State energy particleNumber β μ s by
        field_simp [hβ]]
  rw [exp_neg_beta_mul_effectiveSectorPotential_eq_sectorNumerator
    State energy particleNumber β μ s hβ]

/-- Entropy-regularized sector objective at inverse temperature `β`. -/
noncomputable def sectorVariationalObjective
    (energy : ∀ s, State s → ℝ) (particleNumber : Sector → ℝ)
    (β μ : ℝ) (q : Sector → ℝ) : ℝ :=
  ∑ s, q s * effectiveSectorPotential State energy particleNumber β μ s +
    (1 / β) * ∑ s, q s * Real.log (q s)

/-- The outer variational objective equals grand free energy plus a KL gap. -/
theorem sectorVariationalObjective_eq_grandFreeEnergy_add_relativeEntropy
    (energy : ∀ s, State s → ℝ) (particleNumber : Sector → ℝ)
    {β μ : ℝ} (hβ : 0 < β) (q : Sector → ℝ)
    (hq_pos : ∀ s, 0 < q s) (hq_sum : ∑ s, q s = 1) :
    sectorVariationalObjective State energy particleNumber β μ q =
      grandFreeEnergy State energy particleNumber β μ +
        (1 / β) * finiteRelativeEntropy q
          (sectorWeight State energy particleNumber β μ) := by
  have hβne : β ≠ 0 := ne_of_gt hβ
  have hε : 0 < (1 / β) := one_div_pos.mpr hβ
  have hgeneric :=
    entropyRegularizedObjective_eq_freeEnergy_add_relativeEntropy
      (sectorModel State energy particleNumber β μ) () hε q hq_pos hq_sum
  calc
    sectorVariationalObjective State energy particleNumber β μ q =
        entropyRegularizedObjective
          (sectorModel State energy particleNumber β μ) () (1 / β) q := rfl
    _ = freeEnergy (sectorModel State energy particleNumber β μ) () (1 / β) +
        (1 / β) * finiteRelativeEntropy q
          (weight (sectorModel State energy particleNumber β μ) () (1 / β)) := hgeneric
    _ = grandFreeEnergy State energy particleNumber β μ +
        (1 / β) * finiteRelativeEntropy q
          (sectorWeight State energy particleNumber β μ) := by
      rw [show freeEnergy (sectorModel State energy particleNumber β μ) () (1 / β) =
          grandFreeEnergy State energy particleNumber β μ by
            unfold freeEnergy grandFreeEnergy
            rw [sectorModel_partition_eq_grandPartition
              State energy particleNumber β μ hβne]]
      apply congrArg (fun p => grandFreeEnergy State energy particleNumber β μ +
        (1 / β) * finiteRelativeEntropy q p)
      funext s
      exact sectorModel_weight_eq_sectorWeight
        State energy particleNumber β μ hβne s

/-- The KL term in the sector variational certificate is nonnegative. -/
theorem sectorVariationalGap_nonneg
    (energy : ∀ s, State s → ℝ) (particleNumber : Sector → ℝ)
    {β μ : ℝ} (hβ : 0 < β) (q : Sector → ℝ)
    (hq_pos : ∀ s, 0 < q s) (hq_sum : ∑ s, q s = 1) :
    0 ≤ (1 / β) * finiteRelativeEntropy q
      (sectorWeight State energy particleNumber β μ) := by
  exact mul_nonneg (le_of_lt (one_div_pos.mpr hβ))
    (finiteRelativeEntropy_nonneg q
      (sectorWeight State energy particleNumber β μ)
      hq_pos
      (fun s => by
        unfold sectorWeight sectorNumerator
        exact div_pos
          (mul_pos (Real.exp_pos _) (canonicalPartition_pos State energy β s))
          (grandPartition_pos State energy particleNumber β μ))
      hq_sum
      (sum_sectorWeight_eq_one State energy particleNumber β μ))

/-- The sector Gibbs distribution minimizes the entropy-regularized outer
    objective among positive normalized sector distributions. -/
theorem grandFreeEnergy_le_sectorVariationalObjective
    (energy : ∀ s, State s → ℝ) (particleNumber : Sector → ℝ)
    {β μ : ℝ} (hβ : 0 < β) (q : Sector → ℝ)
    (hq_pos : ∀ s, 0 < q s) (hq_sum : ∑ s, q s = 1) :
    grandFreeEnergy State energy particleNumber β μ ≤
      sectorVariationalObjective State energy particleNumber β μ q := by
  rw [sectorVariationalObjective_eq_grandFreeEnergy_add_relativeEntropy
    State energy particleNumber hβ q hq_pos hq_sum]
  exact le_add_of_nonneg_right
    (sectorVariationalGap_nonneg State energy particleNumber hβ q hq_pos hq_sum)

/-- Equality in the outer variational bound characterizes the sector Gibbs
    distribution among positive normalized sector weights. -/
theorem sectorVariationalObjective_eq_grandFreeEnergy_iff
    (energy : ∀ s, State s → ℝ) (particleNumber : Sector → ℝ)
    {β μ : ℝ} (hβ : 0 < β) (q : Sector → ℝ)
    (hq_pos : ∀ s, 0 < q s) (hq_sum : ∑ s, q s = 1) :
    sectorVariationalObjective State energy particleNumber β μ q =
      grandFreeEnergy State energy particleNumber β μ ↔
      q = sectorWeight State energy particleNumber β μ := by
  rw [sectorVariationalObjective_eq_grandFreeEnergy_add_relativeEntropy
    State energy particleNumber hβ q hq_pos hq_sum]
  have hβne : β ≠ 0 := ne_of_gt hβ
  have hfactor : (1 / β) ≠ 0 := ne_of_gt (one_div_pos.mpr hβ)
  have hp_pos : ∀ s, 0 < sectorWeight State energy particleNumber β μ s := by
    intro s
    unfold sectorWeight sectorNumerator
    exact div_pos
      (mul_pos (Real.exp_pos _) (canonicalPartition_pos State energy β s))
      (grandPartition_pos State energy particleNumber β μ)
  have hp_sum : ∑ s, sectorWeight State energy particleNumber β μ s = 1 :=
    sum_sectorWeight_eq_one State energy particleNumber β μ
  constructor
  · intro h
    have hgap : (1 / β) * finiteRelativeEntropy q
        (sectorWeight State energy particleNumber β μ) = 0 := by
      linarith
    have hkl : finiteRelativeEntropy q
        (sectorWeight State energy particleNumber β μ) = 0 :=
      (mul_eq_zero.mp hgap).resolve_left hfactor
    exact (finiteRelativeEntropy_eq_zero_iff q
      (sectorWeight State energy particleNumber β μ)
      hq_pos hp_pos hq_sum hp_sum).mp hkl
  · intro hq
    have hkl : finiteRelativeEntropy q
        (sectorWeight State energy particleNumber β μ) = 0 := by
      apply (finiteRelativeEntropy_eq_zero_iff q
        (sectorWeight State energy particleNumber β μ)
        hq_pos hp_pos hq_sum hp_sum).mpr
      exact hq
    rw [hkl]
    ring

end HierarchicalGrandCanonical

end InfoGeometry.Canonical
