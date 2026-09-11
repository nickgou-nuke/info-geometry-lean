import InfoGeometry.Projective.ArnoldRelations
import InfoGeometry.Algebra.FiniteSpinAlgebra
import InfoGeometry.Topology.AmplituhedronBoundary
import Mathlib.Data.Fintype.Card
import Mathlib.Tactic

/-!
# Rank-32 Boundary Carrier

This file adds the finite `16 + 16 = 32` carrier used by the
amplituhedron-boundary interface.

Closed here:

* the carrier has exactly `32` indices;
* the first `16` indices are the chiral half;
* the last `16` indices are the anti-chiral half;
* every index is in exactly one of those halves;
* the carrier can be attached to the algebraic three-edge boundary packet.

Not closed here:

* no theorem identifies this carrier with the de Rham cohomology of
  `F_Q(C^4,3)`;
* no theorem identifies these indices with an `N = 4` SYM supermultiplet;
* no linear-independence or spanning theorem for differential forms is asserted.
-/

namespace InfoGeometry.Topology.AmplituhedronBoundary

/-- The finite rank-32 boundary carrier. -/
abbrev BoundaryRank32State := Fin 32

/-- The first sixteen states are the chiral half. -/
def IsChiralState (s : BoundaryRank32State) : Prop :=
  s.val < 16

/-- The last sixteen states are the anti-chiral half. -/
def IsAntiChiralState (s : BoundaryRank32State) : Prop :=
  16 ≤ s.val

/-- The chiral half is explicitly equivalent to `Fin 16`. -/
noncomputable def chiralStateEquivFin16 :
    {s : BoundaryRank32State // IsChiralState s} ≃ Fin 16 where
  toFun s := ⟨s.val.val, s.property⟩
  invFun i := ⟨⟨i.val, by omega⟩, by simp [IsChiralState]⟩
  left_inv := by
    intro s
    cases s with
    | mk val property =>
      cases val with
      | mk v hv =>
        rfl
  right_inv := by
    intro i
    cases i
    rfl

/-- The anti-chiral half is explicitly equivalent to `Fin 16`. -/
noncomputable def antiChiralStateEquivFin16 :
    {s : BoundaryRank32State // IsAntiChiralState s} ≃ Fin 16 where
  toFun s := ⟨s.val.val - 16, by omega⟩
  invFun i := ⟨⟨i.val + 16, by omega⟩, by simp [IsAntiChiralState]⟩
  left_inv := by
    intro s
    cases s with
    | mk val property =>
      cases val with
      | mk v hv =>
        simp [IsAntiChiralState] at property
        apply Subtype.ext
        apply Fin.ext
        simp
        omega
  right_inv := by
    intro i
    cases i with
    | mk v hv =>
      apply Fin.ext
      simp

noncomputable instance : Fintype {s : BoundaryRank32State // IsChiralState s} :=
  Fintype.ofEquiv (Fin 16) chiralStateEquivFin16.symm

noncomputable instance : Fintype {s : BoundaryRank32State // IsAntiChiralState s} :=
  Fintype.ofEquiv (Fin 16) antiChiralStateEquivFin16.symm

/-- The full finite carrier has cardinality `32`. -/
theorem boundaryRank32State_card :
    Fintype.card BoundaryRank32State = 32 := by
  simp [BoundaryRank32State]

/-- The chiral half has cardinality `16`. -/
theorem chiralState_card :
    Fintype.card {s : BoundaryRank32State // IsChiralState s} = 16 := by
  rw [Fintype.card_congr chiralStateEquivFin16]
  simp

/-- The anti-chiral half has cardinality `16`. -/
theorem antiChiralState_card :
    Fintype.card {s : BoundaryRank32State // IsAntiChiralState s} = 16 := by
  rw [Fintype.card_congr antiChiralStateEquivFin16]
  simp

/-- Every rank-32 boundary state is chiral or anti-chiral. -/
theorem chiral_or_antiChiral_state (s : BoundaryRank32State) :
    IsChiralState s ∨ IsAntiChiralState s := by
  unfold IsChiralState IsAntiChiralState
  omega

/-- No rank-32 boundary state is both chiral and anti-chiral. -/
theorem not_chiral_and_antiChiral_state (s : BoundaryRank32State) :
    ¬ (IsChiralState s ∧ IsAntiChiralState s) := by
  unfold IsChiralState IsAntiChiralState
  omega

/--
An explicit rank-32 boundary realization.

The `carrierReadout` field is only an indexed carrier map.  This structure does not
assert that the vectors are a cohomology basis.
-/
structure Rank32BoundaryRealization (Op : Type*) [Ring Op] where
  boundary : Amplituhedron3Point Op
  carrierReadout : BoundaryRank32State → Op

/-! ## Rank-32 Arnold exterior-product carrier -/

/--
The concrete Arnold exterior algebra for the three labelled boundary channels.

This is the finite algebraic exterior carrier only.  It is not a theorem that
this exterior algebra is the de Rham cohomology of `F_Q(C^4,3)`.
-/
abbrev ThreePointArnoldExterior (R : Type*) [CommRing R] :=
  ExteriorAlgebra R
    (InfoGeometry.Projective.Amplituhedron.EdgeModule R (Fin 3))

/-- The Arnold edge generator on the three-point channel set. -/
noncomputable def threePointArnoldW
    (R : Type*) [CommRing R] (i j : Fin 3) :
    ThreePointArnoldExterior R :=
  InfoGeometry.Projective.Amplituhedron.w R (Fin 3) i j

/--
The three Arnold exterior products matching the cyclic boundary channels.

`0` is `ω₀₁ ∧ ω₁₂`, `1` is `ω₁₂ ∧ ω₂₀`, and `2` is
`ω₂₀ ∧ ω₀₁`.
-/
noncomputable def arnoldChannelProduct
    (R : Type*) [CommRing R] (c : Fin 3) :
    ThreePointArnoldExterior R :=
  if c = (0 : Fin 3) then
    threePointArnoldW R 0 1 * threePointArnoldW R 1 2
  else if c = (1 : Fin 3) then
    threePointArnoldW R 1 2 * threePointArnoldW R 2 0
  else
    threePointArnoldW R 2 0 * threePointArnoldW R 0 1

/-- Deterministic projection of the 32 labels onto the three boundary channels. -/
def boundaryRank32Channel (s : BoundaryRank32State) : Fin 3 :=
  ⟨s.val % 3, Nat.mod_lt s.val (by decide)⟩

/--
The canonical Arnold exterior-product readout for each of the 32 labels.

This is a labelled readout, not a basis theorem: no linear independence,
spanning, or de Rham-completeness claim is made here.
-/
noncomputable def boundaryRank32ArnoldProduct
    (R : Type*) [CommRing R] (s : BoundaryRank32State) :
    ThreePointArnoldExterior R :=
  arnoldChannelProduct R (boundaryRank32Channel s)

/--
A rank-32 Arnold exterior-product realization.

The `carrierReadout` name is historical interface terminology: the structure only
asserts that each label reads back as one declared Arnold exterior product.
-/
structure ArnoldProductRank32Realization
    (R : Type*) [CommRing R] where
  carrierReadout : BoundaryRank32State → ThreePointArnoldExterior R
  channel : BoundaryRank32State → Fin 3
  carrier_eq_arnoldChannelProduct :
    ∀ s, carrierReadout s = arnoldChannelProduct R (channel s)

/-- The canonical rank-32 Arnold exterior-product realization. -/
noncomputable def canonicalArnoldProductRank32
    (R : Type*) [CommRing R] :
    ArnoldProductRank32Realization R where
  carrierReadout := boundaryRank32ArnoldProduct R
  channel := boundaryRank32Channel
  carrier_eq_arnoldChannelProduct := by
    intro s
    rfl

namespace ArnoldProductRank32Realization

/-- The Arnold exterior-product carrier has exactly thirty-two labels. -/
theorem label_card
    (R : Type*) [CommRing R] (_B : ArnoldProductRank32Realization R) :
    Fintype.card BoundaryRank32State = 32 :=
  boundaryRank32State_card

/-- Column-matrix form of a rank-32 Arnold exterior-product realization. -/
noncomputable def carrierMatrix
    (R : Type*) [CommRing R]
    (B : ArnoldProductRank32Realization R) :
    Matrix BoundaryRank32State (Fin 1) (ThreePointArnoldExterior R) :=
  fun s _ => B.carrierReadout s

end ArnoldProductRank32Realization

end InfoGeometry.Topology.AmplituhedronBoundary
