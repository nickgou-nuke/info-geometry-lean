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

namespace SplitOctonionG2TwoClassificationBoundary

open InfoGeometry.Algebra.Zorn
open G2TrifactorSU3

variable {R : Type*} [CommRing R]

/-- A candidate finite `G₂(2)`/split-octonion automorphism at the Zorn-coordinate level. -/
structure G2TwoCandidate (cp : ZornCompositionDatum R) where
  map : ZornMatrix R → ZornMatrix R
  /-- Product preservation is an explicit hypothesis, not inferred from the name. -/
  map_mulZ : ∀ X Y : ZornMatrix R, map (cp.mulZ X Y) = cp.mulZ (map X) (map Y)
  /-- The candidate fixes the upper OP projector. -/
  map_OP1 : map (OP1 : ZornMatrix R) = OP1
  /-- The candidate fixes the lower OP projector. -/
  map_OP2 : map (OP2 : ZornMatrix R) = OP2
  /-- Determinant preservation is the finite substitute for norm preservation. -/
  map_detZ : ∀ X : ZornMatrix R,
    ZornMatrix.detZ cp.toCrossProduct3 (map X) = ZornMatrix.detZ cp.toCrossProduct3 X

namespace G2TwoCandidate

variable {cp : ZornCompositionDatum R}
variable (C : G2TwoCandidate cp)

/-- Product preservation readback. -/
theorem preserves_product (X Y : ZornMatrix R) :
    C.map (cp.mulZ X Y) = cp.mulZ (C.map X) (C.map Y) :=
  C.map_mulZ X Y

/-- Determinant preservation readback. -/
theorem preserves_detZ (X : ZornMatrix R) :
    ZornMatrix.detZ cp.toCrossProduct3 (C.map X) = ZornMatrix.detZ cp.toCrossProduct3 X :=
  C.map_detZ X

/-- The candidate preserves the Zorn null cone. -/
theorem preserves_null_cone
    (X : ZornMatrix R)
    (hX : ZornMatrix.IsNull cp.toCrossProduct3 X) :
    ZornMatrix.IsNull cp.toCrossProduct3 (C.map X) := by
  unfold ZornMatrix.IsNull at *
  rw [C.map_detZ X, hX]

/-- If the composition datum uses the repository canonical product, the candidate is OP-stabilizing. -/
theorem isOPStabilizing_for_canonical_zMul
    (hcp : cp.mulZ = zMul) :
    IsOPStabilizingCompositionMap C.map := by
  refine ⟨?_, C.map_OP1, C.map_OP2⟩
  intro X Y
  change C.map (zMul X Y) = zMul (C.map X) (C.map Y)
  rw [← hcp]
  exact C.map_mulZ X Y

/-- Under the canonical-product hypothesis, the candidate preserves the color slot. -/
theorem preserves_colorPart_of_canonical_zMul
    (hcp : cp.mulZ = zMul)
    (X : ZornMatrix R) :
    C.map (colorPart X) = colorPart (C.map X) := by
  exact op_stabilizer_preserves_colorPart C.map
    (C.isOPStabilizing_for_canonical_zMul hcp) X

/-- Under the canonical-product hypothesis, the candidate preserves the anticolor slot. -/
theorem preserves_anticolorPart_of_canonical_zMul
    (hcp : cp.mulZ = zMul)
    (X : ZornMatrix R) :
    C.map (anticolorPart X) = anticolorPart (C.map X) := by
  exact op_stabilizer_preserves_anticolorPart C.map
    (C.isOPStabilizing_for_canonical_zMul hcp) X

/-- Conditional packet of the finite obligations supplied by a candidate. -/
theorem conditional_g2two_boundary_packet
    (hcp : cp.mulZ = zMul) :
    (∀ X Y : ZornMatrix R, C.map (cp.mulZ X Y) = cp.mulZ (C.map X) (C.map Y)) ∧
      (∀ X : ZornMatrix R,
        ZornMatrix.detZ cp.toCrossProduct3 (C.map X) =
          ZornMatrix.detZ cp.toCrossProduct3 X) ∧
      (∀ X : ZornMatrix R, C.map (colorPart X) = colorPart (C.map X)) ∧
      (∀ X : ZornMatrix R, C.map (anticolorPart X) = anticolorPart (C.map X)) := by
  exact ⟨C.preserves_product, C.preserves_detZ,
    C.preserves_colorPart_of_canonical_zMul hcp,
    C.preserves_anticolorPart_of_canonical_zMul hcp⟩

end G2TwoCandidate

end SplitOctonionG2TwoClassificationBoundary

end noncomputable section
