import InfoGeometry.Topology.DelaunayPureBraidRepresentation
import InfoGeometry.Algebra.FiniteSpinAlgebra
import InfoGeometry.Topology.PureBraidGroup
import InfoGeometry.Topology.RohozhkinPBGL

/-!
# Rohozhkin representation boundary

The final representation boundary for Rohozhkin pure-braid representations,
bridging the presented-group descent theorem to the concrete generator
assignment.

This file intentionally does not identify the rational Delaunay transport with
WRT/TQFT, Rokhlin invariants, Majorana zero modes, or a completed nontrivial
Rohozhkin representation.  It records the exact data still needed for that
representation: a concrete generator assignment into rational matrix units and
a proof that all presented pure-braid relators evaluate to `1`.
-/

namespace InfoGeometry.Topology.RohozhkinRepresentation

open InfoGeometry.Topology.RohozhkinBoundary
open InfoGeometry.Topology.PureBraid
open InfoGeometry.Topology.Delaunay

/-- The representation theorem exists when generator matrices satisfy the
presented pure-braid relators. -/
noncomputable def rohozhkinRepresentation (moving : ℕ)
    (gen : PureBraidGenerator (rohozhkinTotalPoints moving) → RohozhkinMatrixUnits moving)
    (hrel : respectsPureBraidRelations gen) :
    RohozhkinPureBraidGroup moving →* RohozhkinMatrixUnits moving :=
  pureBraidMatrixRepresentationOfRelators moving gen hrel

/--
Specification boundary for a nontrivial Rohozhkin/Delaunay braiding
representation.

The closed finite pentagon move lives in `RohozhkinPentagonMatrix`.  This
structure records the separate global descent obligation: the chosen generator
matrices must satisfy every relator in the presented pure-braid group.
-/
structure RohozhkinDelaunayBraidingSpec (moving : ℕ) where
  gen : PureBraidGenerator (rohozhkinTotalPoints moving) → RohozhkinMatrixUnits moving
  relators : respectsPureBraidRelations gen

namespace RohozhkinDelaunayBraidingSpec

/-- A completed Rohozhkin/Delaunay spec descends to the presented pure braid group. -/
noncomputable def representation {moving : ℕ}
    (S : RohozhkinDelaunayBraidingSpec moving) :
    RohozhkinPureBraidGroup moving →* RohozhkinMatrixUnits moving :=
  rohozhkinRepresentation moving S.gen S.relators

/-- Generator readout for the descended representation obtained from a spec. -/
@[simp]
theorem representation_of {moving : ℕ}
    (S : RohozhkinDelaunayBraidingSpec moving)
    (g : PureBraidGenerator (rohozhkinTotalPoints moving)) :
    S.representation (of g) = S.gen g := by
  simp [representation, rohozhkinRepresentation]

/--
Existence packet for the representation supplied by a completed
Rohozhkin/Delaunay spec.
-/
theorem descent_packet {moving : ℕ}
    (S : RohozhkinDelaunayBraidingSpec moving) :
    ∃ ρ : RohozhkinPureBraidGroup moving →* RohozhkinMatrixUnits moving,
      ∀ g : PureBraidGenerator (rohozhkinTotalPoints moving), ρ (of g) = S.gen g := by
  exact ⟨S.representation, S.representation_of⟩

end RohozhkinDelaunayBraidingSpec

end InfoGeometry.Topology.RohozhkinRepresentation
