import InfoGeometry.Algebra.Zorn.SplitOctonionG2TwoClassificationBoundary

/-!
# Split-octonion `Aut(𝕆_s)` / real split `G₂` classification certificate

This file is the theorem-safe landing zone for the requested full
classification.  It does **not** manufacture the classification from a name,
and it does not conflate the finite Chevalley group `G₂(2)` with the real split
form often denoted `G_{2(2)}`.  Instead it states the exact kernel-checkable
certificate needed to promote the slogan

`Aut(𝕆_s(ℝ)) = G₂^{split}(ℝ)`

to a Lean theorem:

* an automorphism group `Aut` acting on the Zorn split-octonion carrier;
* an abstract `G2` group model, to be instantiated by the intended split-real
  or finite carrier;
* a multiplicative equivalence `Aut ≃* G2`;
* explicit product, determinant, OP-projector, and null-cone preservation laws;
* optional finite/root-system invariants matching the GAP/Sage evidence lane.

Supplying such a certificate is the remaining hard classification task.  This
module proves all readbacks from the certificate without adding unsupported
primitive assumptions or pretending that the classification has already been constructed.
-/

noncomputable section

namespace InfoGeometry.Algebra.Zorn.SplitOctonionG2ClassificationCertificate

open InfoGeometry.Algebra.Zorn
open InfoGeometry.Algebra.Zorn.G2TrifactorSU3
open InfoGeometry.Algebra.Zorn.SplitOctonionG2TwoClassificationBoundary

variable {R Aut G2 : Type*} [CommRing R] [Group Aut] [Group G2]

/-- Finite/root-system invariants observed by the GAP/Sage evidence lane. -/
structure G2EvidenceInvariants where
  /-- Sage root-system check: `G₂` has 12 roots. -/
  rootCount : ℕ
  /-- Sage Weyl-group check: `|W(G₂)|=12`. -/
  weylOrder : ℕ
  /-- Sage derivation algebra check for octonion models: dimension 14. -/
  derivationDimension : ℕ
  /-- GAP Atlas finite group check: `|G2(2)|=12096`. -/
  atlasG2TwoOrder : ℕ

/-- The concrete evidence values produced by `tools/sympy/split_octonion_g2_classification_evidence.py`. -/
def computationalEvidenceInvariants : G2EvidenceInvariants where
  rootCount := 12
  weylOrder := 12
  derivationDimension := 14
  atlasG2TwoOrder := 12096

/-- The evidence lane has the expected numerical readouts. -/
theorem computationalEvidenceInvariants_packet :
    computationalEvidenceInvariants.rootCount = 12 ∧
      computationalEvidenceInvariants.weylOrder = 12 ∧
      computationalEvidenceInvariants.derivationDimension = 14 ∧
      computationalEvidenceInvariants.atlasG2TwoOrder = 12096 := by
  exact ⟨rfl, rfl, rfl, rfl⟩

/--
A full classification certificate for `Aut(𝕆_s) = G₂(2)` over the existing
Zorn split-octonion coordinate owner.

`Aut` and `G2` are explicit group carriers.  The multiplicative equivalence is
part of the certificate, together with action laws proving that `Aut` really
acts by split-octonion/Zorn automorphisms.
-/
structure ClassificationCertificate (cp : ZornCompositionDatum R) where
  /-- Action of the automorphism carrier on the Zorn coordinate carrier. -/
  act : Aut → ZornMatrix R → ZornMatrix R
  /-- The identity automorphism acts as identity. -/
  act_one : ∀ X : ZornMatrix R, act 1 X = X
  /-- Group multiplication composes the action. -/
  act_mul : ∀ g h : Aut, ∀ X : ZornMatrix R, act (g * h) X = act g (act h X)
  /-- Every action element preserves the Zorn product. -/
  act_mulZ : ∀ g : Aut, ∀ X Y : ZornMatrix R,
    act g (cp.mulZ X Y) = cp.mulZ (act g X) (act g Y)
  /-- Every action element fixes the upper OP projector. -/
  act_OP1 : ∀ g : Aut, act g (OP1 : ZornMatrix R) = OP1
  /-- Every action element fixes the lower OP projector. -/
  act_OP2 : ∀ g : Aut, act g (OP2 : ZornMatrix R) = OP2
  /-- Every action element preserves the Zorn determinant. -/
  act_detZ : ∀ g : Aut, ∀ X : ZornMatrix R,
    ZornMatrix.detZ cp.toCrossProduct3 (act g X) = ZornMatrix.detZ cp.toCrossProduct3 X
  /-- The actual group-classification equivalence, supplied as certificate data. -/
  autEquivG2 : Aut ≃* G2
  /-- Evidence/invariant ledger attached to the model. -/
  evidence : G2EvidenceInvariants

namespace ClassificationCertificate

variable {cp : ZornCompositionDatum R}
variable (C : ClassificationCertificate (R := R) (Aut := Aut) (G2 := G2) cp)

/-- Read back the supplied classification as a multiplicative equivalence. -/
def aut_equiv_g2
    (C : ClassificationCertificate (R := R) (Aut := Aut) (G2 := G2) cp) :
    Aut ≃* G2 :=
  C.autEquivG2

/-- Every certified automorphism preserves the null cone. -/
theorem act_preserves_null_cone
    (g : Aut)
    (X : ZornMatrix R)
    (hX : ZornMatrix.IsNull cp.toCrossProduct3 X) :
    ZornMatrix.IsNull cp.toCrossProduct3 (C.act g X) := by
  unfold ZornMatrix.IsNull at *
  rw [C.act_detZ g X, hX]

/-- Every certified automorphism determines a `G2TwoCandidate` boundary object. -/
def toG2TwoCandidate (g : Aut) : G2TwoCandidate cp where
  map := C.act g
  map_mulZ := C.act_mulZ g
  map_OP1 := C.act_OP1 g
  map_OP2 := C.act_OP2 g
  map_detZ := C.act_detZ g

/-- Certified automorphisms preserve color slots when the composition datum is canonical. -/
theorem act_preserves_colorPart_of_canonical_zMul
    (hcp : cp.mulZ = zMul (R := R))
    (g : Aut)
    (X : ZornMatrix R) :
    C.act g (colorPart X) = colorPart (C.act g X) := by
  exact (C.toG2TwoCandidate g).preserves_colorPart_of_canonical_zMul hcp X

/-- Certified automorphisms preserve anticolor slots when the composition datum is canonical. -/
theorem act_preserves_anticolorPart_of_canonical_zMul
    (hcp : cp.mulZ = zMul (R := R))
    (g : Aut)
    (X : ZornMatrix R) :
    C.act g (anticolorPart X) = anticolorPart (C.act g X) := by
  exact (C.toG2TwoCandidate g).preserves_anticolorPart_of_canonical_zMul hcp X

/-- Full certificate readback packet with the actual equivalence as data. -/
structure ClassificationReadbackPacket where
  autEquivG2 : Aut ≃* G2
  act_mulZ :
    ∀ g : Aut, ∀ X Y : ZornMatrix R,
      C.act g (cp.mulZ X Y) = cp.mulZ (C.act g X) (C.act g Y)
  act_detZ :
    ∀ g : Aut, ∀ X : ZornMatrix R,
      ZornMatrix.detZ cp.toCrossProduct3 (C.act g X) =
        ZornMatrix.detZ cp.toCrossProduct3 X
  act_preserves_colorPart :
    ∀ g : Aut, ∀ X : ZornMatrix R,
      C.act g (colorPart X) = colorPart (C.act g X)
  act_preserves_anticolorPart :
    ∀ g : Aut, ∀ X : ZornMatrix R,
      C.act g (anticolorPart X) = anticolorPart (C.act g X)

/-- Full certificate readback packet. -/
def classification_certificate_packet
    (hcp : cp.mulZ = zMul (R := R)) :
    C.ClassificationReadbackPacket where
  autEquivG2 := aut_equiv_g2 C
  act_mulZ := C.act_mulZ
  act_detZ := C.act_detZ
  act_preserves_colorPart := C.act_preserves_colorPart_of_canonical_zMul hcp
  act_preserves_anticolorPart := C.act_preserves_anticolorPart_of_canonical_zMul hcp

end ClassificationCertificate

end InfoGeometry.Algebra.Zorn.SplitOctonionG2ClassificationCertificate

end noncomputable section
