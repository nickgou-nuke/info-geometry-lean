import Mathlib
import InfoGeometry.Topology.SymbolicLatentPathHalfRestrictions

namespace InfoGeometry.Topology

/-!
# A theorem-honest interface for path concatenation

The half restrictions are canonical.  A continuous piecewise gluing requires
an endpoint compatibility proof, so this owner packages the gluing property
explicitly rather than pretending that an arbitrary pair of paths has already
been glued.
-/

abbrev SymbolicLatentPathConcatenation
    {X : Type*} [TopologicalSpace X]
    (γ₀ γ₁ : SymbolicLatentPath X) :=
  {γ : SymbolicLatentPath X //
    (∀ t : SymbolicPathDomain,
      γ (symbolicFirstHalfParameter t) = γ₀ t) ∧
    (∀ t : SymbolicPathDomain,
      γ (symbolicSecondHalfParameter t) = γ₁ t)}

namespace SymbolicLatentPathConcatenation

abbrev path
    {X : Type*} [TopologicalSpace X]
    {γ₀ γ₁ : SymbolicLatentPath X}
    (C : SymbolicLatentPathConcatenation γ₀ γ₁) : SymbolicLatentPath X := C.1

abbrev first_half
    {X : Type*} [TopologicalSpace X]
    {γ₀ γ₁ : SymbolicLatentPath X}
    (C : SymbolicLatentPathConcatenation γ₀ γ₁) :
    ∀ t : SymbolicPathDomain,
      C.path (symbolicFirstHalfParameter t) = γ₀ t := C.2.1

abbrev second_half
    {X : Type*} [TopologicalSpace X]
    {γ₀ γ₁ : SymbolicLatentPath X}
    (C : SymbolicLatentPathConcatenation γ₀ γ₁) :
    ∀ t : SymbolicPathDomain,
      C.path (symbolicSecondHalfParameter t) = γ₁ t := C.2.2

end SymbolicLatentPathConcatenation

theorem SymbolicLatentPathConcatenation.compatible_endpoints
    {X : Type*} [TopologicalSpace X]
    {γ₀ γ₁ : SymbolicLatentPath X}
    (C : SymbolicLatentPathConcatenation γ₀ γ₁) :
    γ₀.finish = γ₁.start := by
  have h₀ := C.first_half (1 : SymbolicPathDomain)
  have h₁ := C.second_half (0 : SymbolicPathDomain)
  rw [symbolicFirstHalfParameter_one] at h₀
  rw [symbolicSecondHalfParameter_zero] at h₁
  exact h₀.symm.trans h₁

theorem SymbolicLatentPathConcatenation.start_eq_first_start
    {X : Type*} [TopologicalSpace X]
    {γ₀ γ₁ : SymbolicLatentPath X}
    (C : SymbolicLatentPathConcatenation γ₀ γ₁) :
    C.path.start = γ₀.start := by
  have h := C.first_half (0 : SymbolicPathDomain)
  rw [symbolicFirstHalfParameter_zero] at h
  exact h

theorem SymbolicLatentPathConcatenation.finish_eq_second_finish
    {X : Type*} [TopologicalSpace X]
    {γ₀ γ₁ : SymbolicLatentPath X}
    (C : SymbolicLatentPathConcatenation γ₀ γ₁) :
    C.path.finish = γ₁.finish := by
  have h := C.second_half (1 : SymbolicPathDomain)
  rw [symbolicSecondHalfParameter_one] at h
  exact h

theorem SymbolicLatentPathConcatenation.endpoints_eq
    {X : Type*} [TopologicalSpace X]
    {γ₀ γ₁ : SymbolicLatentPath X}
    (C : SymbolicLatentPathConcatenation γ₀ γ₁) :
    C.path.endpoints = (γ₀.start, γ₁.finish) := by
  ext <;>
    simp [SymbolicLatentPath.endpoints,
      SymbolicLatentPathConcatenation.start_eq_first_start,
      SymbolicLatentPathConcatenation.finish_eq_second_finish]

theorem SymbolicLatentPathConcatenation.midpoint_value
    {X : Type*} [TopologicalSpace X]
    {γ₀ γ₁ : SymbolicLatentPath X}
    (C : SymbolicLatentPathConcatenation γ₀ γ₁) :
    C.path
        (⟨(1 : ℝ) / 2, by constructor <;> norm_num⟩ : SymbolicPathDomain) =
      γ₀.finish := by
  have h := C.first_half (1 : SymbolicPathDomain)
  rw [symbolicFirstHalfParameter_one] at h
  exact h

end InfoGeometry.Topology
