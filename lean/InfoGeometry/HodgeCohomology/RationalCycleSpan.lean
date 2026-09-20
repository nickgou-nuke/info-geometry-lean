import Mathlib.LinearAlgebra.Finsupp.LinearCombination
import Mathlib.LinearAlgebra.Dual.Lemmas

namespace InfoGeometry.HodgeCohomology.RationalCycleSpan

variable {Betti Periods Index : Type*}
variable [AddCommGroup Betti] [Module ℚ Betti]
variable [AddCommGroup Periods] [Module ℚ Periods]

def rationalTypeSubspace (comparison : Betti →ₗ[ℚ] Periods)
    (typeSubspace : Submodule ℚ Periods) : Submodule ℚ Betti :=
  typeSubspace.comap comparison

theorem cycle_span_le_type_subspace
    (comparison : Betti →ₗ[ℚ] Periods) (typeSubspace : Submodule ℚ Periods)
    (cycleClass : Index → Betti)
    (cycleType : ∀ index, comparison (cycleClass index) ∈ typeSubspace) :
    Submodule.span ℚ (Set.range cycleClass) ≤
      rationalTypeSubspace comparison typeSubspace := by
  apply Submodule.span_le.mpr
  rintro vector ⟨index, rfl⟩
  exact cycleType index

theorem cycle_map_surjective_iff_span
    (hodge : Submodule ℚ Betti) (cycleClass : Index → hodge) :
    Function.Surjective (Finsupp.linearCombination ℚ cycleClass) ↔
      Submodule.span ℚ (Set.range fun index => (cycleClass index : Betti)) = hodge := by
  rw [← span_range_eq_top_iff_surjective_finsuppLinearCombination]
  exact Submodule.span_range_subtype_eq_top_iff hodge
    (fun index => (cycleClass index).property)

theorem cycle_map_surjective_iff_dual_detection (cycleClass : Index → Betti) :
    Function.Surjective (Finsupp.linearCombination ℚ cycleClass) ↔
      ∀ functional : Module.Dual ℚ Betti,
        (∀ index, functional (cycleClass index) = 0) → functional = 0 := by
  constructor
  · intro surjective functional vanishes
    ext vector
    obtain ⟨coefficients, rfl⟩ := surjective vector
    rw [Finsupp.apply_linearCombination]
    simp [Function.comp_def, vanishes, Finsupp.linearCombination_apply]
  · intro detects
    rw [← span_range_eq_top_iff_surjective_finsuppLinearCombination]
    apply top_unique
    intro vector _
    apply (Subspace.forall_mem_dualAnnihilator_apply_eq_zero_iff
      (Submodule.span ℚ (Set.range cycleClass)) vector).mp
    intro functional annihilates
    have vanishes : ∀ index, functional (cycleClass index) = 0 := by
      intro index
      exact (Submodule.mem_dualAnnihilator.mp annihilates) (cycleClass index)
        (Submodule.subset_span (Set.mem_range_self index))
    rw [detects functional vanishes]
    rfl

theorem cycle_combinations_preserve_linear_constraints
    (cycleClass : Index → Betti) (constraint : Betti →ₗ[ℚ] Periods)
    (vanishes : ∀ index, constraint (cycleClass index) = 0)
    (coefficients : Index →₀ ℚ) :
    constraint (Finsupp.linearCombination ℚ cycleClass coefficients) = 0 := by
  rw [Finsupp.apply_linearCombination]
  simp [Function.comp_def, vanishes, Finsupp.linearCombination_apply]

theorem missing_constraint_value_obstructs_cycle_representation
    (cycleClass : Index → Betti) (constraint : Betti →ₗ[ℚ] Periods)
    (vanishes : ∀ index, constraint (cycleClass index) = 0)
    (vector : Betti) (nonzero : constraint vector ≠ 0) :
    vector ∉ Submodule.span ℚ (Set.range cycleClass) := by
  intro membership
  have inclusion : Submodule.span ℚ (Set.range cycleClass) ≤ LinearMap.ker constraint := by
    apply Submodule.span_le.mpr
    rintro image ⟨index, rfl⟩
    exact vanishes index
  exact nonzero (inclusion membership)

end InfoGeometry.HodgeCohomology.RationalCycleSpan
