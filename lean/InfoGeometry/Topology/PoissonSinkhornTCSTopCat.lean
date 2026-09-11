import Mathlib
import InfoGeometry.Algebra.FiniteSpinAlgebra
import InfoGeometry.Inference.PoissonSinkhornTCSTopological

/-!
# `TopCat` readouts for the finite Poisson transport kernel

This owner exposes the existing continuous Gibbs assignment and its weighted
transport energy as morphisms in `TopCat`.  The statements remain finite and
explicit: they do not assert Sinkhorn convergence or a Wasserstein supremum.
-/

namespace InfoGeometry.Topology.PoissonSinkhornTCSTopCat

open CategoryTheory
open InfoGeometry.Inference

variable {Observation Component : Type}
  [Fintype Component] [Nonempty Component]

noncomputable def assignmentTopCatHom
    (C : PoissonTransportCost (Observation := Observation)
      (Component := Component)) (i : Observation) (j : Component) :
    TopCat.of NonzeroTemperature ⟶ TopCat.of ℝ :=
  TopCat.ofHom
    { toFun := fun ε => poissonTransportAssignment C (ε : ℝ) i j
      continuous_toFun :=
        continuous_poissonTransportAssignment_temperature C i j }

@[simp] theorem assignmentTopCatHom_apply
    (C : PoissonTransportCost (Observation := Observation)
      (Component := Component)) (i : Observation) (j : Component)
    (ε : NonzeroTemperature) :
    assignmentTopCatHom C i j ε =
      poissonTransportAssignment C (ε : ℝ) i j :=
  rfl

theorem assignmentTopCatHom_pos
    (C : PoissonTransportCost (Observation := Observation)
      (Component := Component)) (i : Observation) (j : Component)
    (ε : NonzeroTemperature) :
    0 < assignmentTopCatHom C i j ε := by
  rw [assignmentTopCatHom_apply]
  exact poissonTransportAssignment_pos C (ε : ℝ) i j

theorem assignmentTopCatHom_row_sum_one
    (C : PoissonTransportCost (Observation := Observation)
      (Component := Component)) (i : Observation)
    (ε : NonzeroTemperature) :
    ∑ j : Component, assignmentTopCatHom C i j ε = 1 := by
  change ∑ j : Component,
      poissonTransportAssignment C (ε : ℝ) i j = 1
  exact poissonTransportAssignment_row_sum_one C (ε : ℝ) i

noncomputable def assignmentVectorTopCatHom
    (C : PoissonTransportCost (Observation := Observation)
      (Component := Component)) (i : Observation) :
    TopCat.of NonzeroTemperature ⟶ TopCat.of (Component → ℝ) :=
  TopCat.ofHom
    { toFun := poissonTransportAssignmentVector C i
      continuous_toFun := continuous_poissonTransportAssignmentVector C i }

theorem assignmentVectorTopCatHom_apply
    (C : PoissonTransportCost (Observation := Observation)
      (Component := Component)) (i : Observation)
    (ε : NonzeroTemperature) :
    assignmentVectorTopCatHom C i ε =
      poissonTransportAssignmentVector C i ε :=
  rfl

section Energy

variable [Fintype Observation] [Nonempty Observation]

noncomputable def assignmentWeightedEnergyTopCatHom
    (C : PoissonTransportCost (Observation := Observation)
      (Component := Component)) :
    TopCat.of NonzeroTemperature ⟶ TopCat.of ℝ :=
  TopCat.ofHom
    { toFun := assignmentWeightedPoissonTransportEnergy C
      continuous_toFun := continuous_assignmentWeightedPoissonTransportEnergy C }

theorem assignmentWeightedEnergyTopCatHom_apply
    (C : PoissonTransportCost (Observation := Observation)
      (Component := Component)) (ε : NonzeroTemperature) :
    assignmentWeightedEnergyTopCatHom C ε =
      assignmentWeightedPoissonTransportEnergy C ε :=
  rfl

end Energy

end InfoGeometry.Topology.PoissonSinkhornTCSTopCat
