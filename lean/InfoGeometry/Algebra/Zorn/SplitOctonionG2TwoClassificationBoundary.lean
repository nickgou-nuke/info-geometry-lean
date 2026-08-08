import InfoGeometry.Algebra.Zorn.G2TrifactorSU3

/-!
# Split-octonion / `G₂(2)` classification boundary

This module records the theorem-safe boundary for the slogan
`Aut(𝕆_s) = G₂(2)`.

It does **not** prove the classification.  Instead it isolates finite
obligations that any future `G₂(2)` candidate must satisfy in the existing Zorn
split-octonion coordinate owner:

* preserve the Zorn product;
* fix the two diagonal OP/trifactor projectors;
* preserve the Zorn determinant/null cone.

From those explicit hypotheses, the candidate commutes with color/anticolor slot
extraction and preserves the null cone.  The actual Lie/group classification of
all split-octonion automorphisms remains closure debt for a separate owner.
-/

noncomputable section

namespace InfoGeometry.Algebra.Zorn.SplitOctonionG2TwoClassificationBoundary

open InfoGeometry.Algebra.Zorn
open G2TrifactorSU3

variable {R : Type*} [CommRing R]

/-- A candidate finite `G₂(2)`/split-octonion automorphism at the Zorn-coordinate level. -/
structure G2TwoCandidate (R : Type*) [CommRing R] where
  map : ZornMatrix R → ZornMatrix R
  /-- Product preservation is an explicit property, not inferred from the name. -/
  map_mulZ : ∀ X Y : ZornMatrix R, map (ZornMatrix.mulZ X Y) = ZornMatrix.mulZ (map X) (map Y)
  /-- The candidate fixes the upper OP projector. -/
  map_OP1 : map (OP1 : ZornMatrix R) = OP1
  /-- The candidate fixes the lower OP projector. -/
  map_OP2 : map (OP2 : ZornMatrix R) = OP2
  /-- Determinant preservation is the finite substitute for norm preservation. -/
  map_detZ : ∀ X : ZornMatrix R,
    ZornMatrix.detZ (map X) = ZornMatrix.detZ X

namespace G2TwoCandidate

variable (C : G2TwoCandidate R)

/-- Product preservation readback. -/
theorem preserves_product (X Y : ZornMatrix R) :
    C.map (ZornMatrix.mulZ X Y) = ZornMatrix.mulZ (C.map X) (C.map Y) :=
  C.map_mulZ X Y

/-- Determinant preservation readback. -/
theorem preserves_detZ (X : ZornMatrix R) :
    ZornMatrix.detZ (C.map X) = ZornMatrix.detZ X :=
  C.map_detZ X

/-- The candidate preserves the Zorn null cone. -/
theorem preserves_null_cone
    (X : ZornMatrix R)
    (hX : ZornMatrix.IsNull X) :
    ZornMatrix.IsNull (C.map X) := by
  unfold ZornMatrix.IsNull at *
  rw [C.map_detZ X, hX]

/-- Since the composition uses the canonical Zorn product, the candidate is OP-stabilizing. -/
theorem isOPStabilizing_for_canonical_zMul :
    IsOPStabilizingCompositionMap C.map := by
  refine ⟨?_, C.map_OP1, C.map_OP2⟩
  intro X Y
  exact C.map_mulZ X Y

/-- Under the canonical-product property, the candidate preserves the color slot. -/
theorem preserves_colorPart_of_canonical_zMul
    (X : ZornMatrix R) :
    C.map (colorPart X) = colorPart (C.map X) := by
  exact op_stabilizer_preserves_colorPart C.map
    C.isOPStabilizing_for_canonical_zMul X

/-- Under the canonical-product property, the candidate preserves the anticolor slot. -/
theorem preserves_anticolorPart_of_canonical_zMul
    (X : ZornMatrix R) :
    C.map (anticolorPart X) = anticolorPart (C.map X) := by
  exact op_stabilizer_preserves_anticolorPart C.map
    C.isOPStabilizing_for_canonical_zMul X

/-- Conditional packet of the finite obligations supplied by a candidate. -/
theorem conditional_g2two_boundary_packet :
    (∀ X Y : ZornMatrix R, C.map (ZornMatrix.mulZ X Y) = ZornMatrix.mulZ (C.map X) (C.map Y)) ∧
      (∀ X : ZornMatrix R,
        ZornMatrix.detZ (C.map X) =
          ZornMatrix.detZ X) ∧
      (∀ X : ZornMatrix R, C.map (colorPart X) = colorPart (C.map X)) ∧
      (∀ X : ZornMatrix R, C.map (anticolorPart X) = anticolorPart (C.map X)) := by
  exact ⟨C.preserves_product, C.preserves_detZ,
    C.preserves_colorPart_of_canonical_zMul,
    C.preserves_anticolorPart_of_canonical_zMul⟩

end G2TwoCandidate

end InfoGeometry.Algebra.Zorn.SplitOctonionG2TwoClassificationBoundary

end noncomputable section
