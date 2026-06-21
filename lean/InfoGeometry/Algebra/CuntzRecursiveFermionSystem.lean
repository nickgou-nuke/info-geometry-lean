import Mathlib.Data.Set.Finite
import Mathlib.Data.Set.Basic
import InfoGeometry.Algebra.KawamuraCuntzCAR

namespace InfoGeometry.Algebra.CuntzRecursiveFermionSystem

/-!
# Maya Diagrams and the Infinite Wedge Representation

Following Katsunori Kawamura, "Extensions of representations of the CAR algebra
to the Cuntz algebra O₂".

We construct the branching functions on the space of Maya diagrams which give
rise to the infinite wedge representation of the CAR algebra and its standard
extension to the Cuntz algebra O₂.
-/

/-- The half-integer lattice Z + 1/2 is mapped to ℤ via `k = j - 1/2`.
    Positive half-integers map to `j ≥ 1`. Negative half-integers map to `j ≤ 0`. -/
abbrev MayaIndex := ℤ

/-- The vacuum state Z_{-/2} = { -1/2, -3/2, ... } corresponding to j ≤ 0. -/
def vacuum : Set MayaIndex := Set.Iic 0

/-- The dual vacuum state Z_{+/2} = { 1/2, 3/2, ... } corresponding to j ≥ 1. -/
def dual_vacuum : Set MayaIndex := Set.Ici 1

/-- A Maya diagram is a subset whose symmetric difference with the vacuum is finite. -/
def IsMaya (S : Set MayaIndex) : Prop :=
  (symmDiff S vacuum).Finite

/-- A Dual Maya diagram is a subset whose symmetric difference with the dual vacuum is finite. -/
def IsDualMaya (S : Set MayaIndex) : Prop :=
  (symmDiff S dual_vacuum).Finite

structure MayaDiagram where
  S : Set MayaIndex
  is_maya : IsMaya S

structure DualMayaDiagram where
  S : Set MayaIndex
  is_dual_maya : IsDualMaya S

/-! ## Branching Functions on Maya Diagrams -/

/-- The S_+ component (positive half-integers). -/
def S_plus (S : Set MayaIndex) : Set MayaIndex :=
  S ∩ Set.Ici 1

/-- The S_- component (negative half-integers). -/
def S_minus (S : Set MayaIndex) : Set MayaIndex :=
  S ∩ Set.Iic 0

/-- The index shift +1, corresponding to `k + 1` on the half-integer lattice. -/
def shift_plus (S : Set MayaIndex) : Set MayaIndex :=
  { j | ∃ i ∈ S, j = i + 1 }

/-- The index negation, corresponding to `-k` on the half-integer lattice.
    Since `k = j - 1/2`, `-k = -j + 1/2 = (1 - j) - 1/2`. -/
def negate_index (S : Set MayaIndex) : Set MayaIndex :=
  { j | ∃ i ∈ S, j = 1 - i }

/-- The branching function g₁ : S ↦ -(S_{+, +1} ∪ S_- ∪ {1/2}) -/
def g1 (S : Set MayaIndex) : Set MayaIndex :=
  negate_index (shift_plus (S_plus S) ∪ (S_minus S) ∪ {1})

/-- The branching function g₂ : S ↦ -(S_{+, +1} ∪ S_-) -/
def g2 (S : Set MayaIndex) : Set MayaIndex :=
  negate_index (shift_plus (S_plus S) ∪ (S_minus S))

/-- Under the Cuntz infinite wedge representation, s₁ acts on Maya diagrams via g₁,
    and s₂ acts via g₂. -/
def wedge_action_s1 (S : MayaDiagram) : DualMayaDiagram :=
  -- g1 applied to a Maya diagram yields a Dual Maya diagram (M_- in the paper)
  sorry 

def wedge_action_s2 (S : MayaDiagram) : DualMayaDiagram :=
  -- g2 applied to a Maya diagram yields a Dual Maya diagram
  sorry

/-! ## Connection to the Recursive Fermion System -/

open InfoGeometry.Algebra

/-- The recursive fermion generators from KawamuraCuntzCAR.
    aₙ = ζ^{n-1}(s₁ s₂*) -/
noncomputable def RFS_fermion {Op : Type*} [Ring Op] [StarRing Op] (C : CuntzO2Carrier Op) (n : ℕ) : Op :=
  kawamuraCARSequence C n

end InfoGeometry.Algebra.CuntzRecursiveFermionSystem
