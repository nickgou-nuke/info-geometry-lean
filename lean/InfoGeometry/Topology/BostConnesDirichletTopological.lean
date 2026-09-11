import Mathlib.Topology.ContinuousMap.Basic
import InfoGeometry.Algebra.FiniteSpinAlgebra
import InfoGeometry.Physics.BostConnesThermalTime

/-!
# Finite topological readouts for the Bost--Connes Dirichlet series

The physics owner defines the individual Dirichlet term and the infinite
series, while explicitly leaving convergence of the latter open.  This file
proves only the corresponding finite topological facts: each term is
continuous in inverse temperature, and every finite cutoff sum is continuous.
-/

noncomputable section

open scoped BigOperators

namespace InfoGeometry.Topology.BostConnesDirichletTopological

open InfoGeometry.Physics.BostConnesThermalTime

theorem continuous_bostConnesDirichletTerm (n : ℕ) :
    Continuous (fun beta : ℝ => bostConnesDirichletTerm beta n) := by
  by_cases hn : n = 0
  · simpa [bostConnesDirichletTerm, hn] using
      (continuous_const : Continuous (fun _ : ℝ => (0 : ℝ)))
  · simp only [bostConnesDirichletTerm, if_neg hn]
    fun_prop

def bostConnesPartialPartitionFunction (modes : Finset ℕ) (beta : ℝ) : ℝ :=
  ∑ n ∈ modes, bostConnesDirichletTerm beta n

theorem continuous_bostConnesPartialPartitionFunction (modes : Finset ℕ) :
    Continuous (bostConnesPartialPartitionFunction modes) := by
  unfold bostConnesPartialPartitionFunction
  refine continuous_finset_sum (s := modes) ?_
  intro n hn
  exact continuous_bostConnesDirichletTerm n

theorem bostConnesPartialPartitionFunction_fiber_isClosed
    (modes : Finset ℕ) (level : ℝ) :
    IsClosed {beta : ℝ |
      bostConnesPartialPartitionFunction modes beta = level} := by
  change IsClosed
    ((bostConnesPartialPartitionFunction modes) ⁻¹' ({level} : Set ℝ))
  exact isClosed_singleton.preimage
    (continuous_bostConnesPartialPartitionFunction modes)

theorem bostConnesPartialPartitionFunction_sublevel_isClosed
    (modes : Finset ℕ) (level : ℝ) :
    IsClosed {beta : ℝ |
      bostConnesPartialPartitionFunction modes beta ≤ level} := by
  change IsClosed
    ((bostConnesPartialPartitionFunction modes) ⁻¹' Set.Iic level)
  exact isClosed_Iic.preimage
    (continuous_bostConnesPartialPartitionFunction modes)

theorem bostConnesPartialPartitionFunction_superlevel_isClosed
    (modes : Finset ℕ) (level : ℝ) :
    IsClosed {beta : ℝ |
      level ≤ bostConnesPartialPartitionFunction modes beta} := by
  change IsClosed
    ((bostConnesPartialPartitionFunction modes) ⁻¹' Set.Ici level)
  exact isClosed_Ici.preimage
    (continuous_bostConnesPartialPartitionFunction modes)

theorem isCompact_bostConnesPartialPartitionFunction_image_Icc
    (modes : Finset ℕ) (a b : ℝ) :
    IsCompact
      (bostConnesPartialPartitionFunction modes '' Set.Icc a b) :=
  isCompact_Icc.image
    (continuous_bostConnesPartialPartitionFunction modes)

theorem isCompact_bostConnesPartialPartitionFunction_sublevel_on_Icc
    (modes : Finset ℕ) (a b level : ℝ) :
    IsCompact
      (Set.Icc a b ∩ {beta : ℝ |
        bostConnesPartialPartitionFunction modes beta ≤ level}) :=
  isCompact_Icc.inter_right
    (bostConnesPartialPartitionFunction_sublevel_isClosed modes level)

theorem isCompact_bostConnesPartialPartitionFunction_superlevel_on_Icc
    (modes : Finset ℕ) (a b level : ℝ) :
    IsCompact
      (Set.Icc a b ∩ {beta : ℝ |
        level ≤ bostConnesPartialPartitionFunction modes beta}) :=
  isCompact_Icc.inter_right
    (bostConnesPartialPartitionFunction_superlevel_isClosed modes level)

theorem exists_min_bostConnesPartialPartitionFunction_on_Icc
    (modes : Finset ℕ) (a b : ℝ) (hab : a ≤ b) :
    ∃ beta ∈ Set.Icc a b,
      ∀ beta' ∈ Set.Icc a b,
        bostConnesPartialPartitionFunction modes beta ≤
          bostConnesPartialPartitionFunction modes beta' := by
  rcases (isCompact_Icc : IsCompact (Set.Icc a b)).exists_isMinOn
      ⟨a, le_rfl, hab⟩
      (continuous_bostConnesPartialPartitionFunction modes).continuousOn
      with ⟨beta, hbeta, hmin⟩
  exact ⟨beta, hbeta, hmin⟩

theorem exists_max_bostConnesPartialPartitionFunction_on_Icc
    (modes : Finset ℕ) (a b : ℝ) (hab : a ≤ b) :
    ∃ beta ∈ Set.Icc a b,
      ∀ beta' ∈ Set.Icc a b,
        bostConnesPartialPartitionFunction modes beta' ≤
          bostConnesPartialPartitionFunction modes beta := by
  have hneg : Continuous
      (fun beta : ℝ => -bostConnesPartialPartitionFunction modes beta) :=
    (continuous_bostConnesPartialPartitionFunction modes).neg
  rcases (isCompact_Icc : IsCompact (Set.Icc a b)).exists_isMinOn
      ⟨a, le_rfl, hab⟩ hneg.continuousOn with
      ⟨beta, hbeta, hmin⟩
  refine ⟨beta, hbeta, ?_⟩
  intro beta' hbeta'
  have h := hmin hbeta'
  exact neg_le_neg_iff.mp h

noncomputable def bostConnesPartialPartitionContinuousMap
    (modes : Finset ℕ) : C(ℝ, ℝ) :=
  ContinuousMap.mk
    (bostConnesPartialPartitionFunction modes)
    (continuous_bostConnesPartialPartitionFunction modes)

@[simp] theorem bostConnesPartialPartitionContinuousMap_apply
    (modes : Finset ℕ) (beta : ℝ) :
    bostConnesPartialPartitionContinuousMap modes beta =
      bostConnesPartialPartitionFunction modes beta :=
  rfl

end InfoGeometry.Topology.BostConnesDirichletTopological
