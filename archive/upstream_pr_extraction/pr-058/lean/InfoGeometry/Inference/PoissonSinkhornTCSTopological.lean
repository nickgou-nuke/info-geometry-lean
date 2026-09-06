import InfoGeometry.Inference.PoissonSinkhornTCSBridge
import InfoGeometry.Inference.PoissonUnbalancedSinkhorn
import InfoGeometry.Inference.PoissonUnbalancedSinkhornTopological

/-!
# Topological readouts for the finite Poisson transport kernel

The row Gibbs assignment is continuous in a nonzero temperature parameter.
This owner records the resulting vector-valued readout and its closed scalar
fibers.  The zero-temperature singularity and numerical Sinkhorn convergence
are intentionally outside this finite statement.
-/

open scoped BigOperators

namespace InfoGeometry.Inference

variable {Observation Component : Type*}
  [Fintype Component] [Nonempty Component]

/-- The parameter space on which division by temperature is continuous. -/
abbrev NonzeroTemperature := {ε : ℝ // ε ≠ 0}

theorem continuous_poissonTransportAssignment_temperature
    (C : PoissonTransportCost (Observation := Observation)
      (Component := Component))
    (i : Observation) (j : Component) :
    Continuous (fun ε : NonzeroTemperature =>
      poissonTransportAssignment C ε i j) := by
  unfold poissonTransportAssignment
  have harg (k : Component) :
      Continuous (fun ε : NonzeroTemperature =>
        -C.cost i k / (ε : ℝ)) := by
    exact (continuous_const :
      Continuous (fun _ : NonzeroTemperature => -C.cost i k)).div
      continuous_subtype_val (fun ε => ε.property)
  have hnum :
      Continuous (fun ε : NonzeroTemperature =>
        Real.exp (-C.cost i j / (ε : ℝ))) :=
    Real.continuous_exp.comp (harg j)
  have hden :
      Continuous (fun ε : NonzeroTemperature =>
        ∑ k : Component, Real.exp (-C.cost i k / (ε : ℝ))) := by
    apply continuous_finset_sum
    intro k hk
    exact Real.continuous_exp.comp (harg k)
  have hden_ne : ∀ ε : NonzeroTemperature,
      (∑ k : Component, Real.exp (-C.cost i k / (ε : ℝ))) ≠ 0 := by
    intro ε
    exact (Finset.sum_pos (fun k _ => Real.exp_pos _)
      Finset.univ_nonempty).ne'
  exact hnum.div hden hden_ne

noncomputable def poissonTransportAssignmentVector
    (C : PoissonTransportCost (Observation := Observation)
      (Component := Component)) (i : Observation) :
    NonzeroTemperature → Component → ℝ :=
  fun ε j => poissonTransportAssignment C ε i j

theorem continuous_poissonTransportAssignmentVector
    (C : PoissonTransportCost (Observation := Observation)
      (Component := Component)) (i : Observation) :
    Continuous (poissonTransportAssignmentVector C i) := by
  exact continuous_pi (fun j =>
    continuous_poissonTransportAssignment_temperature C i j)

theorem poissonTransportAssignmentVector_sum_one
    (C : PoissonTransportCost (Observation := Observation)
      (Component := Component)) (i : Observation)
    (ε : NonzeroTemperature) :
    ∑ j : Component, poissonTransportAssignmentVector C i ε j = 1 := by
  simpa [poissonTransportAssignmentVector] using
    poissonTransportAssignment_row_sum_one C (ε : ℝ) i

theorem poissonTransportAssignmentVector_nonneg
    (C : PoissonTransportCost (Observation := Observation)
      (Component := Component)) (i : Observation)
    (ε : NonzeroTemperature) (j : Component) :
    0 ≤ poissonTransportAssignmentVector C i ε j := by
  exact poissonTransportAssignment_nonneg C (ε : ℝ) i j

theorem poissonTransportAssignment_fiber_isClosed
    (C : PoissonTransportCost (Observation := Observation)
      (Component := Component)) (i : Observation) (j : Component)
    (c : ℝ) :
    IsClosed {ε : NonzeroTemperature |
      poissonTransportAssignmentVector C i ε j = c} := by
  change IsClosed
    ((fun ε : NonzeroTemperature =>
      poissonTransportAssignmentVector C i ε j) ⁻¹' ({c} : Set ℝ))
  exact isClosed_singleton.preimage
    (continuous_poissonTransportAssignment_temperature C i j)

section WeightedEnergy

variable [Fintype Observation] [Nonempty Observation]

theorem continuous_weightedPoissonTransportEnergy
    (C : PoissonTransportCost (Observation := Observation)
      (Component := Component)) :
    Continuous (weightedPoissonTransportEnergy C) := by
  unfold weightedPoissonTransportEnergy
  apply continuous_finset_sum
  intro i hi
  apply continuous_finset_sum
  intro j hj
  have hwij : Continuous
      (fun w : Observation → Component → ℝ => w i j) :=
    (continuous_apply j).comp (continuous_apply i)
  exact hwij.mul continuous_const

theorem weightedPoissonTransportEnergy_sublevel_isClosed
    (C : PoissonTransportCost (Observation := Observation)
      (Component := Component)) (c : ℝ) :
    IsClosed {w : Observation → Component → ℝ |
      weightedPoissonTransportEnergy C w ≤ c} := by
  change IsClosed
    ((weightedPoissonTransportEnergy C) ⁻¹' Set.Iic c)
  exact isClosed_Iic.preimage
    (continuous_weightedPoissonTransportEnergy C)

theorem weightedPoissonTransportEnergy_levelSet_isClosed
    (C : PoissonTransportCost (Observation := Observation)
      (Component := Component)) (c : ℝ) :
    IsClosed {w : Observation → Component → ℝ |
      weightedPoissonTransportEnergy C w = c} := by
  change IsClosed
    ((weightedPoissonTransportEnergy C) ⁻¹' ({c} : Set ℝ))
  exact isClosed_singleton.preimage
    (continuous_weightedPoissonTransportEnergy C)

noncomputable def poissonTransportAssignmentMatrix
    (C : PoissonTransportCost (Observation := Observation)
      (Component := Component)) :
    NonzeroTemperature → Observation → Component → ℝ :=
  fun ε i j => poissonTransportAssignment C (ε : ℝ) i j

theorem continuous_poissonTransportAssignmentMatrix
    (C : PoissonTransportCost (Observation := Observation)
      (Component := Component)) :
    Continuous (poissonTransportAssignmentMatrix C) := by
  exact continuous_pi (fun i =>
    continuous_pi (fun j =>
      continuous_poissonTransportAssignment_temperature C i j))

noncomputable def assignmentWeightedPoissonTransportEnergy
    (C : PoissonTransportCost (Observation := Observation)
      (Component := Component)) :
    NonzeroTemperature → ℝ :=
  fun ε => weightedPoissonTransportEnergy C
    (poissonTransportAssignmentMatrix C ε)

theorem continuous_assignmentWeightedPoissonTransportEnergy
    (C : PoissonTransportCost (Observation := Observation)
      (Component := Component)) :
    Continuous (assignmentWeightedPoissonTransportEnergy C) := by
  exact (continuous_weightedPoissonTransportEnergy C).comp
    (continuous_poissonTransportAssignmentMatrix C)

theorem assignmentWeightedPoissonTransportEnergy_sublevel_isClosed
    (C : PoissonTransportCost (Observation := Observation)
      (Component := Component)) (c : ℝ) :
    IsClosed {ε : NonzeroTemperature |
      assignmentWeightedPoissonTransportEnergy C ε ≤ c} := by
  change IsClosed
    ((assignmentWeightedPoissonTransportEnergy C) ⁻¹' Set.Iic c)
  exact isClosed_Iic.preimage
    (continuous_assignmentWeightedPoissonTransportEnergy C)

noncomputable def poissonTransportCostOnCertificate
    (C : PoissonTransportCost (Observation := Observation)
      (Component := Component)) :
    UnbalancedTransportCertificate (Row := Observation)
      (Col := Component) → ℝ :=
  fun T => weightedPoissonTransportEnergy C T.coupling

theorem continuous_poissonTransportCostOnCertificate
    (C : PoissonTransportCost (Observation := Observation)
      (Component := Component)) :
    Continuous (poissonTransportCostOnCertificate C) := by
  exact (continuous_weightedPoissonTransportEnergy C).comp (by
    fun_prop)

theorem poissonTransportCostOnCertificate_sublevel_isClosed
    (C : PoissonTransportCost (Observation := Observation)
      (Component := Component)) (c : ℝ) :
    IsClosed {T : UnbalancedTransportCertificate
        (Row := Observation) (Col := Component) |
      poissonTransportCostOnCertificate C T ≤ c} := by
  change IsClosed
    ((poissonTransportCostOnCertificate C) ⁻¹' Set.Iic c)
  exact isClosed_Iic.preimage
    (continuous_poissonTransportCostOnCertificate C)

end WeightedEnergy

end InfoGeometry.Inference
