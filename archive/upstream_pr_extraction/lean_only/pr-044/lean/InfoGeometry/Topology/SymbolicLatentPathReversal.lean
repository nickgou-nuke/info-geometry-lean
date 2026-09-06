import Mathlib
import InfoGeometry.Topology.SymbolicLatentPathEndpoints

namespace InfoGeometry.Topology

/-!
The canonical reversal of the compact unit-interval parameter and its action
on symbolic latent paths.
-/

def symbolicPathReversalParameter : C(SymbolicPathDomain, SymbolicPathDomain) :=
  {
    toFun := fun t =>
      ⟨1 - (t : ℝ), by
        constructor <;> linarith [t.property.1, t.property.2]⟩
    continuous_toFun :=
      (continuous_const.sub continuous_subtype_val).subtype_mk (by
        intro t
        constructor <;> linarith [t.property.1, t.property.2])
  }

theorem symbolicPathReversalParameter_apply
    (t : SymbolicPathDomain) :
    symbolicPathReversalParameter t =
      (⟨1 - (t : ℝ), by
        constructor <;> linarith [t.property.1, t.property.2]⟩ :
        SymbolicPathDomain) := rfl

theorem symbolicPathReversalParameter_involutive
    (t : SymbolicPathDomain) :
    symbolicPathReversalParameter
        (symbolicPathReversalParameter t) = t := by
  apply Subtype.ext
  dsimp [symbolicPathReversalParameter]
  ring

theorem symbolicPathReversalParameter_zero :
    symbolicPathReversalParameter 0 = (1 : SymbolicPathDomain) := by
  apply Subtype.ext
  dsimp [symbolicPathReversalParameter]
  norm_num

theorem symbolicPathReversalParameter_one :
    symbolicPathReversalParameter 1 = (0 : SymbolicPathDomain) := by
  apply Subtype.ext
  dsimp [symbolicPathReversalParameter]
  norm_num

def reverseSymbolicLatentPath
    {X : Type*} [TopologicalSpace X]
    (γ : SymbolicLatentPath X) : SymbolicLatentPath X :=
  {
    toFun := fun t => γ (symbolicPathReversalParameter t)
    continuous_toFun := γ.continuous.comp
      symbolicPathReversalParameter.continuous
  }

theorem reverseSymbolicLatentPath_apply
    {X : Type*} [TopologicalSpace X]
    (γ : SymbolicLatentPath X) (t : SymbolicPathDomain) :
    reverseSymbolicLatentPath γ t =
      γ (symbolicPathReversalParameter t) := rfl

theorem reverseSymbolicLatentPath_start
    {X : Type*} [TopologicalSpace X]
    (γ : SymbolicLatentPath X) :
    (reverseSymbolicLatentPath γ).start = γ.finish := by
  change γ (symbolicPathReversalParameter 0) = γ 1
  rw [symbolicPathReversalParameter_zero]

theorem reverseSymbolicLatentPath_finish
    {X : Type*} [TopologicalSpace X]
    (γ : SymbolicLatentPath X) :
    (reverseSymbolicLatentPath γ).finish = γ.start := by
  change γ (symbolicPathReversalParameter 1) = γ 0
  rw [symbolicPathReversalParameter_one]

theorem reverseSymbolicLatentPath_endpoints
    {X : Type*} [TopologicalSpace X]
    (γ : SymbolicLatentPath X) :
    (reverseSymbolicLatentPath γ).endpoints = (γ.finish, γ.start) := by
  ext <;>
    simp [SymbolicLatentPath.endpoints,
      reverseSymbolicLatentPath_start,
      reverseSymbolicLatentPath_finish]

theorem reverse_reverseSymbolicLatentPath
    {X : Type*} [TopologicalSpace X]
    (γ : SymbolicLatentPath X) :
    reverseSymbolicLatentPath (reverseSymbolicLatentPath γ) = γ := by
  ext t
  change γ (symbolicPathReversalParameter
    (symbolicPathReversalParameter t)) = γ t
  rw [symbolicPathReversalParameter_involutive]

end InfoGeometry.Topology
