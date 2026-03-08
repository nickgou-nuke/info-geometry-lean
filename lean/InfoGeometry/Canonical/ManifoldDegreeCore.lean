import InfoGeometry.Canonical.ManifoldHomologyCore
import Mathlib.Data.Int.Basic
import Mathlib.Data.Real.Basic
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.Topology.Basic
import Mathlib.Topology.Order

/-!
# InfoGeometry.Canonical.ManifoldDegreeCore

Canonical manifold-degree primitives in explicit finite/discrete settings.
-/

namespace InfoGeometry.Canonical.ManifoldDegree

variable {M : Type*}

/-- On finite carriers, every fiber is finite. -/
theorem preimage_finite (f : M → M) (y : M) [Fintype M] :
    (f ⁻¹' ({y} : Set M)).Finite := by
  exact Set.toFinite _

/--
In a discrete topology, singleton neighborhoods isolate a chosen preimage point.
This gives a concrete replacement for the old assumption-backed isolation lemma.
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

/-- Integer-valued sign extracted from a Jacobian determinant in finite dimension. -/
noncomputable def localDegreeSign {n : ℕ}
    (A : Matrix (Fin n) (Fin n) ℝ) : ℤ :=
  if 0 ≤ A.det then 1 else -1

/-- The local degree sign always evaluates to `1` or `-1`. -/
theorem localDegreeSign_eq_one_or_neg_one {n : ℕ}
    (A : Matrix (Fin n) (Fin n) ℝ) :
    localDegreeSign A = 1 ∨ localDegreeSign A = -1 := by
  by_cases h : 0 ≤ A.det
  · left
    simp [localDegreeSign, h]
  · right
    simp [localDegreeSign, h]

/--
If the fiber over `y` is finite, it is a regular value in the canonical manifold-homology core.
-/
theorem regularValue_of_finite_preimage
    (f : M → M) (y : M)
    (h : (f ⁻¹' ({y} : Set M)).Finite) :
    InfoGeometry.Canonical.ManifoldHomology.IsRegularValue f y :=
  h

end InfoGeometry.Canonical.ManifoldDegree
