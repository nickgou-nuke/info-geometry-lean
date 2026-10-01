import InfoGeometry.Canonical.SpinorialCore.Algebra

/-!
# Finite-dimensional index and the trivalent counting defect

This is a kernel/cokernel index of a specified linear map. It is not a
continuum Atiyah-Singer theorem, a Pin bordism computation, or a charge map.
-/

namespace InfoGeometry.Canonical.SpinorialCore

section LinearIndex
variable {K E F : Type*} [Field K]
  [AddCommGroup E] [Module K E] [FiniteDimensional K E]
  [AddCommGroup F] [Module K F] [FiniteDimensional K F]

noncomputable def finiteIndex (f : E →ₗ[K] F) : ℤ :=
  (Module.finrank K (LinearMap.ker f) : ℤ) -
    (Module.finrank K (F ⧸ LinearMap.range f) : ℤ)

/-- Rank-nullity supplies the finite index; the map is not assumed invertible. -/
theorem finiteIndex_eq_dimension_difference (f : E →ₗ[K] F) :
    finiteIndex f = (Module.finrank K E : ℤ) - (Module.finrank K F : ℤ) := by
  have hr := LinearMap.finrank_range_add_finrank_ker f
  have hq := Submodule.finrank_quotient_add_finrank (LinearMap.range f)
  unfold finiteIndex
  omega

end LinearIndex

/-- Signed defect, using integer subtraction rather than truncated subtraction. -/
def vertexDefect (black white : ℕ) : ℤ := (black : ℤ) - (white : ℤ)

/-- Consequence of the two explicit graph-counting hypotheses. -/
theorem trivalent_helicity_defect (black white edges external : ℕ) (k : ℤ)
    (hhandshake : 3 * black + 3 * white = 2 * edges + external)
    (hk : k = 2 * (black : ℤ) + (white : ℤ) - (edges : ℤ)) :
    2 * k - (external : ℤ) = vertexDefect black white := by
  unfold vertexDefect
  omega

theorem paired_vertex_insertion_invariant (black white pairs : ℕ) :
    vertexDefect (black + pairs) (white + pairs) = vertexDefect black white := by
  unfold vertexDefect
  omega

/-- The actual grading matrix of the specified finite bipartite carrier. -/
def vertexGrading (black white : ℕ) :
    Matrix (Fin black ⊕ Fin white) (Fin black ⊕ Fin white) ℤ :=
  Matrix.diagonal (Sum.elim (fun _ => 1) (fun _ => -1))

theorem vertexGrading_trace (black white : ℕ) :
    Matrix.trace (vertexGrading black white) = vertexDefect black white := by
  simp [vertexGrading, vertexDefect, Matrix.trace_diagonal]

/-- A non-vacuous bridge: the network map is an arbitrary supplied linear map. -/
theorem network_index_eq_trace {K : Type*} [Field K] (black white : ℕ)
    (D : (Fin black → K) →ₗ[K] (Fin white → K)) :
    finiteIndex D = Matrix.trace (vertexGrading black white) := by
  rw [finiteIndex_eq_dimension_difference, vertexGrading_trace]
  simp [vertexDefect]

end InfoGeometry.Canonical.SpinorialCore
