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

section Finite

variable [Fintype X]

/-- Total partition function before coarse graining. -/
noncomputable def totalPartition (energy : X → ℝ) (β : ℝ) : ℝ :=
  ∑ x, boltzmannWeight energy β x

end Finite

section Fiber

variable [Fintype X] [DecidableEq Y]

/-- Partition function restricted to one retained coarse fiber. -/
noncomputable def fiberPartition
    (G : FiniteCoarseGraining X Y) (energy : X → ℝ) (β : ℝ) (y : Y) : ℝ :=
  G.fiberWeight (boltzmannWeight energy β) y

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
  FiniteCoarseGraining.trivial α

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
  exact (FiniteCoarseGraining.fiberWeight_trivial_eq_totalWeight
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
  exact (FiniteCoarseGraining.fiberWeight_trivial_eq_totalWeight
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
