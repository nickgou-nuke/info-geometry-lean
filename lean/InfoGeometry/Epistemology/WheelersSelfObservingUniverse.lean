import Mathlib.LinearAlgebra.Projection
import Mathlib.Analysis.InnerProductSpace.Symmetric
import Mathlib.Tactic

namespace InfoGeometry.Epistemology.WheelersSelfObservingUniverse

section Module

variable {Scalar Space : Type*} [Ring Scalar] [AddCommGroup Space] [Module Scalar Space]
variable (projection : Module.End Scalar Space) (idempotent : IsIdempotentElem projection)

theorem projected_is_fixed (state : Space) :
    projection (projection state) = projection state := by
  exact congrArg (fun operator : Module.End Scalar Space => operator state) idempotent.eq

theorem range_iff_fixed (state : Space) :
    state ∈ LinearMap.range projection ↔ projection state = state :=
  idempotent.mem_range_iff

theorem remainder_mem_kernel (state : Space) :
    state - projection state ∈ LinearMap.ker projection := by
  change projection (state - projection state) = 0
  rw [map_sub, projected_is_fixed projection idempotent, sub_self]

theorem range_kernel_complementary :
    IsCompl (LinearMap.range projection) (LinearMap.ker projection) :=
  idempotent.isCompl

theorem decomposition (state : Space) :
    projection state + (state - projection state) = state := by abel

theorem decomposition_components_unique (state observed hidden : Space)
    (observed_fixed : projection observed = observed)
    (hidden_killed : projection hidden = 0) (reconstruct : observed + hidden = state) :
    observed = projection state ∧ hidden = state - projection state := by
  have observed_eq : observed = projection state := by
    rw [← reconstruct, map_add, observed_fixed, hidden_killed, add_zero]
  refine ⟨observed_eq, ?_⟩
  rw [← observed_eq, ← reconstruct]
  abel

theorem exists_unique_decomposition (state : Space) :
    ∃! components : Space × Space,
      projection components.1 = components.1 ∧ projection components.2 = 0 ∧
        components.1 + components.2 = state := by
  refine ⟨(projection state, state - projection state), ?_, ?_⟩
  · exact ⟨projected_is_fixed projection idempotent state,
      remainder_mem_kernel projection idempotent state, decomposition projection state⟩
  · intro components properties
    exact Prod.ext
      (decomposition_components_unique projection state components.1 components.2
        properties.1 properties.2.1 properties.2.2).1
      (decomposition_components_unique projection state components.1 components.2
        properties.1 properties.2.1 properties.2.2).2

theorem no_remainder_iff_fixed (state : Space) :
    state - projection state = 0 ↔ projection state = state := by
  rw [sub_eq_zero, eq_comm]

theorem fixed_and_kernel_iff_zero (state : Space) :
    (projection state = state ∧ projection state = 0) ↔ state = 0 := by
  constructor
  · rintro ⟨fixed, killed⟩
    exact fixed.symm.trans killed
  · rintro rfl
    simp

end Module

section InnerProduct

variable {Space : Type*} [NormedAddCommGroup Space] [InnerProductSpace ℝ Space]

theorem range_kernel_orthogonal_of_symmetric (projection : Module.End ℝ Space)
    (symmetric : projection.IsSymmetric) (observed hidden : Space)
    (observed_mem : observed ∈ LinearMap.range projection)
    (hidden_mem : hidden ∈ LinearMap.ker projection) :
    inner (𝕜 := ℝ) observed hidden = 0 := by
  obtain ⟨preimage, rfl⟩ := observed_mem
  rw [symmetric preimage hidden, LinearMap.mem_ker.mp hidden_mem, inner_zero_right]

end InnerProduct

end InfoGeometry.Epistemology.WheelersSelfObservingUniverse
