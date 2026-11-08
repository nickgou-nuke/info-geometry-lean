import Mathlib.Topology.Basic
import InfoGeometry.Algebra.FiniteSpinAlgebra
import Mathlib.Order.Basic
import InfoGeometry.Causal.ProofTopology

open Set

namespace InfoGeometry.Causal

open ProofTopology

variable {α : Type*} [Preorder α]

/-- A subset is an upper set if it is upward closed. -/
def IsUpperSet (s : Set α) : Prop :=
  ∀ ⦃a b⦄, a ∈ s → a ≤ b → b ∈ s

/-- Alexandrov topology on a preorder. -/
def AlexandrovTopology : TopologicalSpace α where
  IsOpen := IsUpperSet
  isOpen_univ := by
    intro a b _ _
    trivial
  isOpen_inter := by
    intro s t hs ht a b ha hab
    exact ⟨hs ha.1 hab, ht ha.2 hab⟩
  isOpen_sUnion := by
    intro S hS a b ha hab
    rcases ha with ⟨u, huS, hau⟩
    exact ⟨u, huS, hS u huS hau hab⟩

/-- The forward cone is open in the Alexandrov topology. -/
theorem forwardCone_open (a : α) :
    @IsOpen α AlexandrovTopology (forwardCone a) := by
  intro x y (hx : a ≤ x) (hxy : x ≤ y)
  exact le_trans hx hxy

end InfoGeometry.Causal
