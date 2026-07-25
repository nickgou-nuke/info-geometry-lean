import InfoGeometry.Canonical.CoarseGraining
import InfoGeometry.GrandCanonical.Core
import Mathlib.Analysis.SpecialFunctions.Log.Basic

open scoped BigOperators

namespace InfoGeometry.Canonical

/-!
# Partition Hierarchy

Finite coarse-grained Boltzmann/Gibbs partition calculus.

This module isolates the nucleus theorem schema:

`effectivePotential = -(1 / β) * log (fiber partition after coarse graining)`.
-/

namespace PartitionHierarchy

open InfoGeometry.GrandCanonical

variable {X Y α : Type*}

/-- Microscopic Boltzmann weight for an energy observable. -/
noncomputable def boltzmannWeight (energy : X → ℝ) (β : ℝ) (x : X) : ℝ :=
  Real.exp (-β * energy x)

/-- Every microscopic Boltzmann weight is strictly positive. -/
theorem boltzmannWeight_pos (energy : X → ℝ) (β : ℝ) (x : X) :
    0 < boltzmannWeight energy β x :=
  Real.exp_pos _

section Finite

variable [Fintype X]

/-- Total partition function before coarse graining. -/
noncomputable def totalPartition (energy : X → ℝ) (β : ℝ) : ℝ :=
  ∑ x, boltzmannWeight energy β x

/-- A finite nonempty microscopic state space has a strictly positive partition function. -/
theorem totalPartition_pos [Nonempty X] (energy : X → ℝ) (β : ℝ) :
    0 < totalPartition energy β := by
  classical
  unfold totalPartition
  exact Finset.sum_pos
    (fun x _ => boltzmannWeight_pos energy β x)
    Finset.univ_nonempty

end Finite

section Fiber

variable [Fintype X] [DecidableEq Y]

/-- Partition function restricted to one retained coarse fiber. -/
noncomputable def fiberPartition
    (G : FiniteCoarseGraining X Y) (energy : X → ℝ) (β : ℝ) (y : Y) : ℝ :=
  G.fiberWeight (boltzmannWeight energy β) y

/-- Every coarse fiber partition is nonnegative, including an empty fiber. -/
theorem fiberPartition_nonneg
    (G : FiniteCoarseGraining X Y) (energy : X → ℝ) (β : ℝ) (y : Y) :
    0 ≤ fiberPartition G energy β y := by
  classical
  unfold fiberPartition FiniteCoarseGraining.fiberWeight
  exact Finset.sum_nonneg (fun x _ => le_of_lt (boltzmannWeight_pos energy β x))

/-- A coarse fiber containing a microscopic state has strictly positive partition function. -/
theorem fiberPartition_pos
    (G : FiniteCoarseGraining X Y) (energy : X → ℝ) (β : ℝ) (y : Y)
    (hy : ∃ x, G.project x = y) :
    0 < fiberPartition G energy β y := by
  classical
  rcases hy with ⟨x, hx⟩
  let xFiber : {x // G.project x = y} := ⟨x, hx⟩
  unfold fiberPartition FiniteCoarseGraining.fiberWeight
  exact Finset.sum_pos
    (fun x _ => boltzmannWeight_pos energy β x)
    ⟨xFiber, Finset.mem_univ xFiber⟩

/-- Log-partition potential on a retained coarse fiber. -/
noncomputable def logPartitionPotential
    (G : FiniteCoarseGraining X Y) (energy : X → ℝ) (β : ℝ) (y : Y) : ℝ :=
  Real.log (fiberPartition G energy β y)

/-- Effective free-energy-style potential induced by coarse graining. -/
noncomputable def effectivePotential
    (G : FiniteCoarseGraining X Y) (energy : X → ℝ) (β : ℝ) (y : Y) : ℝ :=
  -(1 / β) * logPartitionPotential G energy β y

/-- The effective potential is exactly `-(1/β) log` of the coarse fiber partition. -/
@[simp] theorem effectivePotential_eq_neg_inv_temp_mul_log_fiberPartition
    (G : FiniteCoarseGraining X Y) (energy : X → ℝ) (β : ℝ) (y : Y) :
    effectivePotential G energy β y =
      -(1 / β) * Real.log (fiberPartition G energy β y) := rfl

/-- Exponentiating a populated fiber's log-partition potential recovers its partition. -/
theorem exp_logPartitionPotential_eq_fiberPartition
    (G : FiniteCoarseGraining X Y) (energy : X → ℝ) (β : ℝ) (y : Y)
    (hy : ∃ x, G.project x = y) :
    Real.exp (logPartitionPotential G energy β y) =
      fiberPartition G energy β y := by
  unfold logPartitionPotential
  exact Real.exp_log (fiberPartition_pos G energy β y hy)

/--
At nonzero inverse temperature, exponentiating `-β` times the effective
potential recovers the populated fiber partition.
-/
theorem exp_neg_temp_mul_effectivePotential_eq_fiberPartition
    (G : FiniteCoarseGraining X Y) (energy : X → ℝ) (β : ℝ) (y : Y)
    (hβ : β ≠ 0)
    (hy : ∃ x, G.project x = y) :
    Real.exp (-β * effectivePotential G energy β y) =
      fiberPartition G energy β y := by
  rw [effectivePotential_eq_neg_inv_temp_mul_log_fiberPartition]
  have hcancel :
      -β * (-(1 / β) * Real.log (fiberPartition G energy β y)) =
        Real.log (fiberPartition G energy β y) := by
    field_simp [hβ]
  rw [hcancel]
  exact Real.exp_log (fiberPartition_pos G energy β y hy)

end Fiber

section FiniteHierarchy

variable [Fintype X] [Fintype Y] [DecidableEq Y]

/-- The coarse partition hierarchy exactly redistributes total weight over fibers. -/
theorem totalPartition_eq_sum_fiberPartition
    (G : FiniteCoarseGraining X Y) (energy : X → ℝ) (β : ℝ) :
    totalPartition energy β = ∑ y, fiberPartition G energy β y := by
  unfold totalPartition fiberPartition
  simpa using
    (FiniteCoarseGraining.totalWeight_eq_sum_fiberWeight
      (G := G) (w := boltzmannWeight energy β))

end FiniteHierarchy

section GrandCanonicalSpecialization

variable [Fintype α]

/-- Trivial one-cell coarse graining of a finite grand-canonical model. -/
def grandCanonicalTrivialCoarse : FiniteCoarseGraining α PUnit :=
  FiniteCoarseGraining.singleton α

/-- The grand-canonical partition is the total microscopic Boltzmann partition. -/
@[simp] theorem grandCanonical_partition_eq_totalPartition
    (params : GrandCanonicalParams α) (β : ℝ) :
    GrandCanonical.partition params β = totalPartition params.energy β := rfl

/-- The grand-canonical partition is the fiber partition of the trivial coarse level. -/
@[simp] theorem grandCanonical_partition_eq_trivialFiberPartition
    (params : GrandCanonicalParams α) (β : ℝ) :
    GrandCanonical.partition params β =
      fiberPartition grandCanonicalTrivialCoarse params.energy β PUnit.unit := by
  rw [grandCanonical_partition_eq_totalPartition]
  exact (FiniteCoarseGraining.fiberWeight_singleton_eq_totalWeight
    (X := α) (w := boltzmannWeight params.energy β)).symm

/-- The grand-canonical log potential is the trivial-level coarse log-partition potential. -/
@[simp] theorem grandCanonical_potential_eq_trivialLogPartitionPotential
    (params : GrandCanonicalParams α) (β : ℝ) :
    GrandCanonical.potential params β =
      logPartitionPotential grandCanonicalTrivialCoarse params.energy β PUnit.unit := by
  rw [GrandCanonical.potential, grandCanonical_partition_eq_trivialFiberPartition]
  rfl

/-- Grand-canonical free energy is `-(1/β)` times the trivial-level log partition. -/
@[simp] theorem grandCanonical_freeEnergy_eq_trivialEffectivePotential
    (params : GrandCanonicalParams α) (β : ℝ) :
    -(1 / β) * GrandCanonical.potential params β =
      effectivePotential grandCanonicalTrivialCoarse params.energy β PUnit.unit := by
  rw [grandCanonical_potential_eq_trivialLogPartitionPotential]
  rfl

/-- Two-parameter grand-canonical partition is a trivial fiber partition of shifted energy. -/
@[simp] theorem grandCanonical_partitionGC_eq_trivialFiberPartition
    (params : GrandCanonicalTwoParam α) (β μ : ℝ) :
    GrandCanonical.partitionGC params β μ =
      fiberPartition grandCanonicalTrivialCoarse (fun x => GrandCanonical.shiftedEnergy params μ x)
        β PUnit.unit := by
  rw [GrandCanonical.partitionGC]
  exact (FiniteCoarseGraining.fiberWeight_singleton_eq_totalWeight
    (X := α)
    (w := boltzmannWeight (fun x => GrandCanonical.shiftedEnergy params μ x) β)).symm

/-- Two-parameter grand-canonical log potential is a trivial coarse log-partition potential. -/
@[simp] theorem grandCanonical_potentialGC_eq_trivialLogPartitionPotential
    (params : GrandCanonicalTwoParam α) (β μ : ℝ) :
    GrandCanonical.potentialGC params β μ =
      logPartitionPotential grandCanonicalTrivialCoarse
        (fun x => GrandCanonical.shiftedEnergy params μ x) β PUnit.unit := by
  rw [GrandCanonical.potentialGC, grandCanonical_partitionGC_eq_trivialFiberPartition]
  rfl

end GrandCanonicalSpecialization

end PartitionHierarchy

end InfoGeometry.Canonical
