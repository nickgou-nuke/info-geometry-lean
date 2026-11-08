import Mathlib
import InfoGeometry.Algebra.FiniteSpinAlgebra
import InfoGeometry.Topology.SymbolicLatentPathHomotopy
import InfoGeometry.Topology.SymbolicLatentPathReversal

namespace InfoGeometry.Topology

/-!
# Reversal of endpoint-preserving symbolic-latent homotopies

Reversal acts on the homotopy parameter and leaves the path parameter fixed.
The endpoint conditions needed for the reversed property follow from the
homotopy's existing endpoint-invariance lemmas.
-/

def symbolicPathSquareHomotopyReversal : C(SymbolicPathSquare, SymbolicPathSquare) :=
  { toFun := fun p => (symbolicPathReversalParameter p.1, p.2)
    continuous_toFun :=
      (symbolicPathReversalParameter.continuous.comp continuous_fst).prodMk
        continuous_snd }

@[simp] theorem symbolicPathSquareHomotopyReversal_apply
    (p : SymbolicPathSquare) :
    symbolicPathSquareHomotopyReversal p =
      (symbolicPathReversalParameter p.1, p.2) :=
  rfl

def reverseSymbolicLatentPathHomotopy
    {X : Type*} [TopologicalSpace X]
    {γ₀ γ₁ : SymbolicLatentPath X}
    (H : SymbolicLatentPathHomotopy γ₀ γ₁) :
    SymbolicLatentPathHomotopy γ₁ γ₀ where
  map := H.map.comp symbolicPathSquareHomotopyReversal
  at_start := by
    intro t
    change H.map (symbolicPathReversalParameter 0, t) = γ₁ t
    rw [symbolicPathReversalParameter_zero]
    exact H.at_finish t
  at_finish := by
    intro t
    change H.map (symbolicPathReversalParameter 1, t) = γ₀ t
    rw [symbolicPathReversalParameter_one]
    exact H.at_start t
  fixed_start := by
    intro s
    change H.map (symbolicPathReversalParameter s, 0) = γ₁.start
    exact (H.fixed_start _).trans H.same_start
  fixed_finish := by
    intro s
    change H.map (symbolicPathReversalParameter s, 1) = γ₁.finish
    exact (H.fixed_finish _).trans H.same_finish

theorem reverseSymbolicLatentPathHomotopy_same_endpoints
    {X : Type*} [TopologicalSpace X]
    {γ₀ γ₁ : SymbolicLatentPath X}
    (H : SymbolicLatentPathHomotopy γ₀ γ₁) :
    γ₁.endpoints = γ₀.endpoints := by
  exact Prod.ext
    (reverseSymbolicLatentPathHomotopy H).same_start
    (reverseSymbolicLatentPathHomotopy H).same_finish

theorem reverse_reverseSymbolicLatentPathHomotopy
    {X : Type*} [TopologicalSpace X]
    {γ₀ γ₁ : SymbolicLatentPath X}
    (H : SymbolicLatentPathHomotopy γ₀ γ₁) :
    reverseSymbolicLatentPathHomotopy
      (reverseSymbolicLatentPathHomotopy H) = H := by
  cases H with
  | mk map at_start at_finish fixed_start fixed_finish =>
    have hmap :
        (map.comp symbolicPathSquareHomotopyReversal).comp
            symbolicPathSquareHomotopyReversal = map := by
      ext p
      change map
          (symbolicPathReversalParameter
            (symbolicPathReversalParameter p.1), p.2) = map p
      rw [symbolicPathReversalParameter_involutive]
    rw [SymbolicLatentPathHomotopy.mk.injEq]
    exact hmap

end InfoGeometry.Topology
