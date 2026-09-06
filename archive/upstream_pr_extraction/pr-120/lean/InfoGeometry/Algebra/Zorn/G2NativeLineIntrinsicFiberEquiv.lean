import InfoGeometry.Algebra.Zorn.G2NativeCandidateSymmetry
import InfoGeometry.Algebra.Zorn.G2NativeLineFiberTransport
import InfoGeometry.Algebra.Zorn.G2NativeFullFlagAction
import InfoGeometry.Algebra.Zorn.G2IntrinsicBaseFlag
import InfoGeometry.Algebra.Zorn.G2NativeCandidateFiberAction
import InfoGeometry.Algebra.Zorn.G2IntrinsicBaseFlag

/-!
# Native and intrinsic base-line fibres

The two line carriers are connected through the already proved quotient
equivalences.  This owner records only the resulting finite-type
equivalence.  It deliberately does not assert equivariance: that is a
separate compatibility theorem.
-/

namespace InfoGeometry.Algebra.Zorn.G2NativeLineIntrinsicFiberEquiv

open InfoGeometry.Algebra.Zorn.G2NativeCandidateSymmetry
open InfoGeometry.Algebra.Zorn.G2NativeLineSetQuotient
open InfoGeometry.Algebra.Zorn.G2NativeLineFiber
open InfoGeometry.Algebra.Zorn.G2InvariantIncidenceCandidates
open InfoGeometry.Algebra.Zorn.G2ImaginaryOctImBridge
open InfoGeometry.Algebra.Zorn.G2NativeOnePointStabilizer
open InfoGeometry.Algebra.Zorn.G2NativeBaseFiber
open InfoGeometry.Algebra.Zorn.G2NativeLineFiberTransport
open InfoGeometry.Algebra.Zorn.G2IntrinsicBaseFlag
open InfoGeometry.Algebra.Zorn.G2ParabolicLineAction
open InfoGeometry.Algebra.Zorn.G2IntrinsicBaseFlag
open InfoGeometry.OperatorAlgebra.G2TwoAutomorphismTheorem

theorem cast_intrinsicLine_val_image
    {p q : OctImIsotropicPoint} (h : p = q)
    (L : IntrinsicLine p) :
    (cast (congrArg IntrinsicLine h) L).1.image Subtype.val =
      L.1.image Subtype.val := by
  cases h
  rfl

theorem zornZeroTripleMap_val_image_eq_lineSet_action
    (g : SplitOctF2Aut)
    (hg : octImAction g nativeBasePoint = nativeBasePoint)
    (y : G2ParabolicLineCarrier.OctImF2)
    (hy : nativeCandidateAt nativeBasePoint y) :
    (zornZeroTripleMap g
      (intrinsicLineOfNativeCandidate y hy).1).image Subtype.val =
      lineSet (octImAction g y) := by
  rw [zornZeroTripleMap_val_image, lineSet_action g hg y]
  rw [← intrinsicLineOfNativeCandidate_val_image_eq_lineSet y hy]
  rw [Finset.image_image]
  rfl

theorem octImAction_fix_nativeBasePoint_implies_octImPointPerm_fix
    (g : SplitOctF2Aut)
    (hg : octImAction g nativeBasePoint = nativeBasePoint) :
    octImPointPerm g nativeBaseIsotropicPoint =
      nativeBaseIsotropicPoint := by
  rw [octImPointPerm_apply]
  apply Subtype.ext
  change octImAction g nativeBasePoint = nativeBasePoint
  exact hg

theorem intrinsicLineOfNativeCandidate_action_eq_cast
    (g : SplitOctF2Aut)
    (hg : octImAction g nativeBasePoint = nativeBasePoint)
    (hgp : octImPointPerm g nativeBaseIsotropicPoint =
      nativeBaseIsotropicPoint)
    (y : G2ParabolicLineCarrier.OctImF2)
    (hy : nativeCandidateAt nativeBasePoint y) :
    intrinsicLineOfNativeCandidate (octImAction g y)
        (nativeCandidateAt_map_of_fix g hg y hy) =
      cast (congrArg IntrinsicLine hgp)
        (intrinsicLineMap g (intrinsicLineOfNativeCandidate y hy)) := by
  apply Subtype.ext
  apply Finset.map_injective ⟨Subtype.val, Subtype.val_injective⟩
  simp only [Finset.map_eq_image]
  change (intrinsicLineOfNativeCandidate (octImAction g y) _).1.image
      Subtype.val =
    (cast (congrArg IntrinsicLine hgp)
      (intrinsicLineMap g (intrinsicLineOfNativeCandidate y hy))).1.image
        Subtype.val
  rw [intrinsicLineOfNativeCandidate_val_image_eq_lineSet,
    cast_intrinsicLine_val_image hgp, intrinsicLineMap_val,
    zornZeroTripleMap_val_image]
  calc
    lineSet (octImAction g y) =
        (lineSet y).image (octImAction g) := lineSet_action g hg y
    _ = ((intrinsicLineOfNativeCandidate y hy).1.image Subtype.val).image
        (octImAction g) := by
      rw [intrinsicLineOfNativeCandidate_val_image_eq_lineSet y hy]
    _ = (intrinsicLineOfNativeCandidate y hy).1.image
      (fun v => octImAction g v.1) := by
      rw [Finset.image_image]
      rfl

theorem nativeLineQuotientToIntrinsicLine_action_eq_cast
    (g : SplitOctF2Aut)
    (hg : octImAction g nativeBasePoint = nativeBasePoint)
    (hgp : octImPointPerm g nativeBaseIsotropicPoint =
      nativeBaseIsotropicPoint)
    (q : nativeLineQuotient) :
    nativeLineQuotientToIntrinsicLine
        (nativeLineQuotientAction g hg q) =
      cast (congrArg IntrinsicLine hgp)
        (intrinsicLineMap g (nativeLineQuotientToIntrinsicLine q)) := by
  induction q using Quotient.inductionOn with
  | h y =>
    have hy : nativeCandidateAt nativeBasePoint y.1 := by
      exact (Finset.mem_filter.mp y.2).2
    change nativeLineQuotientToIntrinsicLine
        (nativeLineQuotientAction g hg (Quotient.mk' y)) =
      cast (congrArg IntrinsicLine hgp)
        (intrinsicLineMap g
          (nativeLineQuotientToIntrinsicLine (Quotient.mk' y)))
    rw [nativeLineQuotientAction_mk,
      nativeLineQuotientToIntrinsicLine_mk]
    exact intrinsicLineOfNativeCandidate_action_eq_cast g hg hgp y.1 hy

theorem lineSetQuotientToNativeLines_action
    (g : SplitOctF2Aut)
    (hg : octImAction g nativeBasePoint = nativeBasePoint)
    (q : nativeLineQuotient) :
    lineSetQuotientToNativeLines (nativeLineQuotientAction g hg q) =
      nativeLineAction g hg (lineSetQuotientToNativeLines q) := by
  induction q using Quotient.inductionOn with
  | h y =>
    change nativeLineOfQuotient
        (nativeLineQuotientAction g hg (Quotient.mk' y)) =
      nativeLineAction g hg (nativeLineOfQuotient (Quotient.mk' y))
    rw [nativeLineQuotientAction_mk]
    apply Subtype.ext
    exact lineSet_action g hg y.1

noncomputable def nativeLineToIntrinsicLineEquiv :
    NativeLine ≃ IntrinsicLine
      G2NativeOnePointStabilizer.nativeBaseIsotropicPoint :=
  lineSetQuotientToNativeLines.symm.trans
    nativeLineQuotientIntrinsicLineEquiv

theorem nativeLineToIntrinsicLineEquiv_val_image (L : NativeLine) :
    (nativeLineToIntrinsicLineEquiv L).1.image Subtype.val = L.1 := by
  change (nativeLineQuotientToIntrinsicLine (quotientOfNativeLine L)).1.image Subtype.val = L.1
  rw [show quotientOfNativeLine L =
      Quotient.mk' (nativeCandidateOfLine L) from rfl]
  rw [nativeLineQuotientToIntrinsicLine_mk]
  rw [intrinsicLineOfNativeCandidate_val_image_eq_lineSet]
  exact nativeCandidateOfLine_spec L

theorem nativeLineToIntrinsicLineEquiv_lineZero :
    nativeLineToIntrinsicLineEquiv lineZero = baseIntrinsicLine := by
  apply Subtype.ext
  ext v
  rw [mem_baseIntrinsicLine_iff]
  have himage :
      (nativeLineToIntrinsicLineEquiv lineZero).1.image Subtype.val =
        lineZero.1 := by
    change
      (nativeLineQuotientToIntrinsicLine
          (lineSetQuotientToNativeLines.symm lineZero)).1.image Subtype.val =
        lineZero.1
    rw [show lineSetQuotientToNativeLines.symm lineZero =
        Quotient.mk' (nativeCandidateOfLine lineZero) from rfl]
    rw [nativeLineQuotientToIntrinsicLine_mk]
    rw [intrinsicLineOfNativeCandidate_val_image_eq_lineSet]
    exact nativeCandidateOfLine_spec lineZero
  constructor
  · intro hv
    have hv' :
        v.1 ∈ (nativeLineToIntrinsicLineEquiv lineZero).1.image Subtype.val :=
      Finset.mem_image_of_mem Subtype.val hv
    rwa [himage] at hv'
  · intro hv
    have hv' :
        v.1 ∈ (nativeLineToIntrinsicLineEquiv lineZero).1.image Subtype.val := by
      rwa [himage]
    rcases Finset.mem_image.mp hv' with ⟨w, hw, heq⟩
    have hvw : v = w := Subtype.ext heq.symm
    rwa [hvw]

theorem nativeLineToIntrinsicLineEquiv_surjective :
    Function.Surjective
      (nativeLineToIntrinsicLineEquiv : NativeLine →
        IntrinsicLine G2NativeOnePointStabilizer.nativeBaseIsotropicPoint) :=
  nativeLineToIntrinsicLineEquiv.surjective

theorem nativeLineToIntrinsicLineEquiv_injective :
    Function.Injective
      (nativeLineToIntrinsicLineEquiv : NativeLine →
        IntrinsicLine G2NativeOnePointStabilizer.nativeBaseIsotropicPoint) :=
  nativeLineToIntrinsicLineEquiv.injective

theorem nativeLineToIntrinsicLineEquiv_action_eq_cast
    (g : SplitOctF2Aut)
    (hg : octImAction g nativeBasePoint = nativeBasePoint)
    (hgp : octImPointPerm g nativeBaseIsotropicPoint =
      nativeBaseIsotropicPoint)
    (L : NativeLine) :
    nativeLineToIntrinsicLineEquiv (nativeLineAction g hg L) =
      cast (congrArg IntrinsicLine hgp)
        (intrinsicLineMap g (nativeLineToIntrinsicLineEquiv L)) := by
  dsimp [nativeLineToIntrinsicLineEquiv]
  let q : nativeLineQuotient := lineSetQuotientToNativeLines.symm L
  have hq : lineSetQuotientToNativeLines.symm (nativeLineAction g hg L) =
      nativeLineQuotientAction g hg q := by
    apply lineSetQuotientToNativeLines.injective
    rw [lineSetQuotientToNativeLines.apply_symm_apply]
    rw [lineSetQuotientToNativeLines_action]
    dsimp [q]
    rw [lineSetQuotientToNativeLines.apply_symm_apply]
  change nativeLineQuotientToIntrinsicLine (lineSetQuotientToNativeLines.symm (nativeLineAction g hg L)) =
    cast (congrArg IntrinsicLine hgp)
      (intrinsicLineMap g (nativeLineQuotientToIntrinsicLine q))
  rw [hq]
  exact nativeLineQuotientToIntrinsicLine_action_eq_cast g hg hgp q

end InfoGeometry.Algebra.Zorn.G2NativeLineIntrinsicFiberEquiv
