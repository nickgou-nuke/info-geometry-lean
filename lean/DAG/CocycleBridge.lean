/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import DAG.GraphHodge
import DAG.HodgeTheorems
import DAG.TwoComplex

/-!
# DAG.CocycleBridge

Bridge data for packaging the computable Hodge invariants of a `TwoComplex`.
The executable owners are `DAG.TwoComplex`, `DAG.GraphHodge`, and the concrete
checks in `DAG.HodgeTheorems`. This file is a readout/packaging layer, not a
continuous Connes-cocycle theorem owner.
-/

open DAG

namespace DAG.CocycleBridge

/-- The rank-based first Betti count, truncated to `Nat`, is at most the number
of edge coordinates. This is the finite-dimensional bound used by downstream
correspondence readouts. -/
theorem betti1_toNat_le_edgeCount {α : Type} [BEq α] [Hashable α]
    (tc : TwoComplex α) : (betti1 tc).toNat ≤ tc.edges.size := by
  have hle : betti1 tc ≤ Int.ofNat tc.edges.size := by
    simp only [betti1]
    have hr1 : 0 ≤ Int.ofNat (gaussianRank (boundary1 tc)) := Int.natCast_nonneg _
    have hr2 : 0 ≤ Int.ofNat (gaussianRank (boundary2 tc)) := Int.natCast_nonneg _
    omega
  simpa using Int.toNat_le_toNat hle

/-- A finite Hodge readout is determined by its source complex; all numerical
invariants below are derived, so a package cannot store inconsistent values. -/
structure HodgeCocycleData (α : Type) [BEq α] [Hashable α] where
  complex : TwoComplex α
  deriving Repr

namespace HodgeCocycleData

/-- First Betti count from the rank formula, truncated to `Nat`. -/
def betti1 {α : Type} [BEq α] [Hashable α] (hd : HodgeCocycleData α) : Nat :=
  (DAG.betti1 hd.complex).toNat

/-- Euler characteristic computed from the underlying finite complex. -/
def eulerChar {α : Type} [BEq α] [Hashable α] (hd : HodgeCocycleData α) : Int :=
  eulerCharacteristic hd.complex

/-- Hodge rank/nullity readout computed from the underlying finite complex. -/
def hodgeDecomp {α : Type} [BEq α] [Hashable α]
    (hd : HodgeCocycleData α) : Nat × Nat × Nat :=
  ( gaussianRank (matTranspose (boundary1 hd.complex))
  , gaussianRank (boundary2 hd.complex)
  , betti1Hodge hd.complex )

/-- The derived first Betti count is bounded by the number of edge coordinates. -/
theorem betti1_le_edges {α : Type} [BEq α] [Hashable α]
    (hd : HodgeCocycleData α) : hd.betti1 ≤ hd.complex.edges.size :=
  betti1_toNat_le_edgeCount hd.complex

/-- The Hodge nullity coordinate is bounded by its ambient edge-coordinate
space. -/
theorem hodgeHarmonicDim_le_edges {α : Type} [BEq α] [Hashable α]
    (hd : HodgeCocycleData α) : hd.hodgeDecomp.2.2 ≤ hd.complex.edges.size := by
  change betti1Hodge hd.complex ≤ hd.complex.edges.size
  unfold betti1Hodge
  exact Nat.sub_le _ _

end HodgeCocycleData

/-- Construct HodgeCocycleData from any TwoComplex. -/
def fromTwoComplex {α : Type} [BEq α] [Hashable α] (tc : TwoComplex α) :
    HodgeCocycleData α :=
  { complex := tc }

/-
Analytic or categorical identifications with continuous cocycles must be proved
by an owner theorem outside this finite readout layer.
-/

end DAG.CocycleBridge
