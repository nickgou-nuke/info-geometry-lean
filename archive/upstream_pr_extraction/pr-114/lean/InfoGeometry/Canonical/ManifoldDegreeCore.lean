import InfoGeometry.Canonical.ManifoldHomologyCore
import Mathlib.Analysis.Calculus.FDeriv.Basic
import Mathlib.Data.Int.Basic
import Mathlib.Data.Real.Basic
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.Topology.Basic
import Mathlib.Topology.Order

/-!
# InfoGeometry.Canonical.ManifoldDegreeCore

Canonical manifold-degree primitives leveraging differential geometry.
Transitioned from discrete encodings to Jacobian-based local degree signs.
-/

namespace InfoGeometry.Canonical.ManifoldDegree

variable {M : Type*} [NormedAddCommGroup M] [NormedSpace ℝ M] [FiniteDimensional ℝ M]

set_option linter.unusedSectionVars false in
/--
Isolating preimages in a discrete topology (legacy support).
On a continuous manifold, this would be provided by the Inverse Function Theorem.
-/
theorem exists_isolating_nhds_of_discrete
    [TopologicalSpace M] (hdisc : DiscreteTopology M)
    (f : M → M) {x y : M} (hx : f x = y) :
    ∃ U : Set M, IsOpen U ∧ x ∈ U ∧ (U ∩ f ⁻¹' ({y} : Set M) = {x}) := by
  letI : DiscreteTopology M := hdisc
  refine ⟨{x}, isOpen_discrete _, by simp, ?_⟩
  ext z
  constructor
  · intro hz
    rcases hz with ⟨hzU, _hzPre⟩
    simpa using hzU
  · intro hz
    refine ⟨?_, ?_⟩
    · simp [hz]
    · have hz' : z = x := by simpa using hz
      simp [hz', hx]

/--
The local degree sign is the sign of the Jacobian determinant.
This is the canonical definition for Phase 1.
-/
noncomputable def localDegreeSign (f : M → M) (x : M) : ℤ :=
  InfoGeometry.Canonical.ManifoldHomology.localDegreeSign f x

set_option linter.unusedSectionVars false in
/--
A point is a regular value if the Jacobian is non-vanishing at all preimages.
-/
theorem regularValue_of_nonvanishing_jacobian
    (f : M → M) (y : M)
    (h : ∀ x, f x = y → LinearMap.det (fderiv ℝ f x).toLinearMap ≠ 0) :
    InfoGeometry.Canonical.ManifoldHomology.IsRegularValue f y := by
  exact h

/--
Mapping degree at a regular value `y` with a finite fiber.
-/
noncomputable def mappingDegree (f : M → M) (y : M) (hy : InfoGeometry.Canonical.ManifoldHomology.IsRegularValue f y)
    (hfinite : (f ⁻¹' ({y} : Set M)).Finite) : ℤ :=
  InfoGeometry.Canonical.ManifoldHomology.mappingDegree f y hy hfinite

end InfoGeometry.Canonical.ManifoldDegree
