import InfoGeometry.OperatorAlgebra.ComplexBoundedOperators.FiniteMatrix
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Topology.Algebra.Module.Equiv
import Mathlib.LinearAlgebra.Span.Defs

/-!
# One-dimensional complex bounded-operator adapter

AFP `One_Dimensional_Spaces` introduces a custom `one_dim` class and proves
that such spaces are canonically isomorphic to `ℂ`.

The Lean-native executable/model space for this role is the one-coordinate
coordinate space `Unit → ℂ`, with the canonical continuous linear equivalence
to `ℂ` supplied by mathlib as `ContinuousLinearEquiv.funUnique`.
-/

noncomputable section

namespace InfoGeometry.OperatorAlgebra.ComplexBoundedOperators
namespace OneDimensional

open FiniteMatrix

/-- The concrete one-dimensional complex coordinate space. -/
abbrev OneDimSpace : Type :=
  FinKetSpace Unit

/-- The unique coordinate ket. -/
def oneKet : OneDimSpace :=
  ketPi ()

/-- Canonical continuous linear equivalence `Unit → ℂ ≃L[ℂ] ℂ`. -/
def oneDimIso : OneDimSpace ≃L[ℂ] ℂ :=
  (EuclideanSpace.equiv Unit ℂ).trans (ContinuousLinearEquiv.funUnique Unit ℂ ℂ)

@[simp]
theorem oneDimIso_apply (x : OneDimSpace) :
    oneDimIso x = x () :=
  by rfl

@[simp]
theorem oneDimIso_symm_apply (z : ℂ) (u : Unit) :
    oneDimIso.symm z u = z := by
  cases u
  rfl

@[simp]
theorem oneKet_apply (u : Unit) :
    oneKet u = 1 := by
  cases u
  simp [oneKet, ketPi]

/-- Every vector in the one-dimensional coordinate space is its coordinate times `oneKet`. -/
theorem oneDim_decompose (x : OneDimSpace) :
    (oneDimIso x) • oneKet = x := by
  ext u
  cases u
  simp [oneKet, ketPi]

/-- The unique ket spans the one-dimensional coordinate space. -/
theorem span_oneKet_eq_top :
    Submodule.span ℂ ({oneKet} : Set OneDimSpace) = ⊤ := by
  apply le_antisymm
  · exact le_top
  · intro x _
    rw [Submodule.mem_span_singleton]
    exact ⟨oneDimIso x, oneDim_decompose x⟩

/-- A continuous linear map out of a one-dimensional coordinate space is determined by `oneKet`. -/
theorem continuousLinearMap_ext_oneKet
    {F : Type*} [NormedAddCommGroup F] [NormedSpace ℂ F]
    {S T : OneDimSpace →L[ℂ] F}
    (h : S oneKet = T oneKet) :
    S = T := by
  ext x
  rw [← oneDim_decompose x]
  simp [h]

end OneDimensional
end InfoGeometry.OperatorAlgebra.ComplexBoundedOperators
